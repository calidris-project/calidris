{-|
Module      : Resolver
Description : Resolves names within files
Copyright   : (c) TrueBoxGuy, 2022
License     : MIT
Maintainer  : https://github.com/TrueBoxGuy
Stability   : experimental
Portability : portable

Processes import statements within files to convert a list of 
'FileContents' to a global list of 'MainStatement's, with names 
of constants being replaced by unique integers, and 
bound names being replaced by De Bruijn indices.
-}
module Resolver where

import Control.Monad.State.Lazy
import Data.Bifunctor
import Data.Foldable
import Data.Function
import Data.Functor
import Data.List
import Data.Map (Map, (!))
import qualified Data.Map as M
import Data.Maybe

import Error
import Syntax

-- | Type used to give each constant a name that is globally unique,
-- and bound variables names based on De Bruijn indices. 
data ResolvedName 
  = UniqueName Integer 
   -- ^ An integer value for a constant that is guaranteed to be unique. 
   | Binding 
   -- ^ A variable that becomes bound, such as @x@ in @forall x : T, x@. 
   -- No extra information needs to be stored for this variable, 
   -- as De Bruijn levels are used.
   | Index Integer
   -- ^ The name bound by the binding n levels up 
   -- from the expression, where n is 0 indexed.
    deriving (Eq, Ord, Show)

-- * Validity checks

-- | Gives a list of at least two elements
-- for which the key function gives the same 
-- value.
findDupBy :: Ord b => (a -> b) -> [a] -> Maybe [a]
findDupBy f = find ((> 1) . length) . groupBy ((==) `on` f) . sortOn f

-- | Ensures that no two files have the same module name.
-- Throws 'ModuleDuplicationError' otherwise.
checkDuplicateModule :: [FileContents] -> Either CustomBundle () 
checkDuplicateModule contents =
  case findDupBy (annVal . moduleName) contents of
    Just (m1 : _) -> let mn = moduleName m1 in
      Left (mkBundleError (ModuleDuplicationError (annVal mn)) mn)
    _ -> pure ()

-- | Ensures that the introduction of a name does not overlap with
-- a previously defined name. Throws 'ShadowingError' otherwise.
checkShadowing
  :: Map [String] a -- ^ A map containing the defined names.
  -> LocAnn x -- ^ The location where the name is introduced. 
  -> [String] -- ^ The name being introduced.
  -> Either CustomBundle ()
checkShadowing context ann x = case M.lookup x context of 
    Nothing -> pure () 
    Just _ -> Left $ mkBundleError (ShadowingError x) ann

-- * Conversion functions.

-- | Given a state, assigns, for each name in each module, 
-- a globally unique integer name. 
assignNamesState
  :: [FileContents] 
  -> State Integer [([String], [([String], Integer)])]  
assignNamesState = 
  traverse
    ( \fc -> do
        integerAssignments <-
          traverse
            ( \ms -> do
                index <- get
                modify (+ 1)
                pure (extractDef ms, index)
            ) 
            (mainStmts fc)
        pure (annVal . moduleName $ fc, integerAssignments)
    )

-- | Assigns unique names to each name in each file. 
makeNameMapping 
  :: [FileContents] 
  -> Map [String] [([String], Integer)] 
  -- ^ A mapping from module name to the names within that module
  -- and their associated unique integers.
makeNameMapping contents = M.fromList $ evalState (assignNamesState contents) 0
    
-- | Introduces all the qualified names from an import, 
-- and checks these names do not overlap previously 
-- defined names. Throws 'FindModuleError' if a module
-- can not be found.
introduceImport 
  :: Map [String] [([String], Integer)] 
    -- ^ A mapping from module names to names within that module
    -- and their unique integer assignments. 
  -> Map [String] Integer
    -- ^ A mapping containing names already defined within the scope. 
  -> LocAnn ImportStatement
  -> Either CustomBundle (Map [String] Integer)
introduceImport moduleMapping context ann =
  do
    let mn = importName . annVal $ ann
        prep = importAs . annVal $ ann
        introName c (nm, i) 
          = checkShadowing c ann nm $> M.insert nm i c
    case M.lookup mn moduleMapping of
      Nothing -> Left (mkBundleError (FindModuleError mn) ann)
      Just mapping -> foldM introName context (first (prep <>) <$> mapping)

-- | Converts the names within an expression to 'ResolvedName's. 
convertExpr 
  :: Map [String] Integer 
    -- ^ The file namespace: a mapping from names to unique integers. 
  -> Expr [String] 
  -> Either CustomBundle (Expr ResolvedName)
convertExpr = go 0 . fmap UniqueName
    where 
      contextIntro cons lvl c ann e1 e2 =
        let x = annVal ann
            nC = M.insert x (Index lvl) c
            -- To calculate De Bruijn level 
         in cons    (Binding <$ ann) 
                <$> go lvl c e1
                <*> (checkShadowing c ann (annVal ann) *> go (lvl + 1) nC e2)
      go _ _ Set = pure Set
      go _ _ Prop = pure Prop
      go _ _ (Type i) = pure (Type i)
      go lvl c (Identifier x) =
        case M.lookup (annVal x) c of
          Nothing -> Left (mkBundleError UndefinedError x)
          Just v -> pure . Identifier $ v <$ x
      go lvl c (Forall x e1 e2) = contextIntro Forall lvl c x e1 e2
      go lvl c (Abs x e1 e2) = contextIntro Abs lvl c x e1 e2
      go lvl c (Let ann e1 e2 e3) =
        do
          newType <- traverse (go lvl c) e1
          newDef <- go lvl c e2
          checkShadowing c ann (annVal ann)
          newE <- go (lvl + 1) (M.insert (annVal ann) (Index lvl) c) e3
          pure $ Let (Binding <$ ann) newType newDef newE
      go lvl c (App a b) = App <$> go lvl c a <*> go lvl c b

-- | Converts the names within a main statement to 'ResolvedName's. 
convertStatement 
  :: Map [String] Integer 
    -- ^ The file namespace: a mapping from names to unique integers. 
  -> MainStatement [String]
  -> Either CustomBundle (MainStatement ResolvedName)
convertStatement context (Assume ann t) =
  Assume (UniqueName . (context !) <$> ann) <$> convertExpr context t
convertStatement context (Define ann t e) =
  Define (UniqueName . (context !) <$> ann) 
    <$> traverse (convertExpr context) t <*> convertExpr context e

-- | Converts the names within a module to 'ResolvedName's. 
moduleToMainStatements 
  :: Map [String] [([String], Integer)]
  -- ^ The result of 'makeNameMapping' on all file contents.
  -> FileContents 
  -> Either CustomBundle [MainStatement ResolvedName]
moduleToMainStatements moduleMapping fc =
  do
    initialC <- foldM (introduceImport moduleMapping) M.empty (importStmts fc)
    let curNames = M.fromList $ moduleMapping ! (annVal . moduleName $ fc)
    let introName c stmt =
          let annNm = extractAnnDef stmt; nm = extractDef stmt
           in checkShadowing c annNm nm $> M.insert nm (curNames M.! nm) c
    context <- foldM introName initialC (mainStmts fc)
    traverse (convertStatement context) (mainStmts fc)

-- | Converts a list of 'FileContents' to a global list of 
-- @'MainStatement' 'ResolvedName'@.
toMainStatements :: [FileContents] -> Either CustomBundle [MainStatement ResolvedName]
toMainStatements contents = do 
  checkDuplicateModule contents
  let mapping = makeNameMapping contents
  concat <$> traverse (moduleToMainStatements mapping) contents
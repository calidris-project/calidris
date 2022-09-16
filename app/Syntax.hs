{-|
Module      : Syntax
Description : Data types for language syntax
Copyright   : (c) TrueBoxGuy, 2022
License     : MIT
Maintainer  : https://github.com/TrueBoxGuy
Stability   : experimental
Portability : portable

Data types representing the syntax of the programming language, 
as well as data types for annotating source locations. 
-}
{-# LANGUAGE DeriveTraversable #-}
module Syntax where

import Data.List
import Text.Megaparsec

-- | An expression in the language.
data Expr x
  = -- | The Set type.
    Set
  | -- | The Prop type.
    Prop
  | -- | The Type(i) type.
    -- The types are 0 indexed.
    Type Integer
  | -- | A variable or constant in the language.
    Identifier (LocAnn x)
  | -- | The expression @forall x : T, U@.
    Forall
      (LocAnn x)
      -- ^ The name of the variable bound in U.
      (Expr x)
      -- ^ The type T of the variable bound.
      (Expr x)
      -- ^ The type U.
  | -- | The expression @fun x : T, u@.
    Abs
      (LocAnn x)
      -- ^ The name of the variable bound in u.
      (Expr x)
      -- ^ The type T of the variable bound.
      (Expr x)
      -- ^ The expression u.
  | -- | The expression @let x : T = t in u@ or @let x = t in u@.
    Let
      (LocAnn x)
      -- ^ The name of the variable bound in u.
      (Maybe (Expr x))
      -- ^ The type T.
      (Expr x)
      -- ^ The expression t.
      (Expr x)
      -- ^ The expression u.
  | -- | An application of two expressions.
    App (Expr x) (Expr x)
  deriving (Eq, Foldable, Functor, Traversable)

-- | An annotation to help throwing errors at
-- a specific code location.
data LocAnn x = LocAnn
  { -- | State stored to convert offsets to inputs. 
    annPosState :: PosState String,
    -- | The offset where parsing of the item began.
    annOffset :: Int,
    -- | The length of the item parsed.
    annLen :: Int,
    annVal :: x
  } | NoLoc {annVal :: x}
  deriving (Eq, Foldable, Functor, Traversable)

-- | A statement to introduce identifiers from 
-- other modules into the namespace. 
data ImportStatement = -- | The statement @import module as name@ or @import module@.
  Import
  { -- | The name of the module to import.
    importName :: [String],
    -- | Potentially empty list of qualifiers
    -- to prepend to the identifiers imported.
    importAs :: [String]
  }
  deriving (Eq, Ord)

-- | The main statements in the file. 
data MainStatement x = Assume -- ^ A type assumption @x : T@. 
 (LocAnn x) -- ^ The variable x. 
 (Expr x) -- ^ The type T.
  | Define -- ^ A declaration, of form either @x = y@ or, to verify the type of the expression, 
  -- @x : T = y@.
  (LocAnn x) -- ^ The variable x. 
   (Maybe (Expr x)) -- ^ The optional type T. 
   (Expr x) -- ^ The expression y
   deriving Eq

-- | Get the variable being defined by a 'MainStatement',
-- alongside its 'LocAnn'.
extractAnnDef :: MainStatement x -> LocAnn x 
extractAnnDef (Assume x _) = x 
extractAnnDef (Define x _ _) = x

-- | Get the variable being defined by a 'MainStatement'.
extractDef :: MainStatement x -> x
extractDef = annVal . extractAnnDef

-- | The information contained in a file. 
data FileContents =
  FileContents
  { -- | The name of the module to associate the file to.
    moduleName :: LocAnn [String],
    -- | The imports within the file.
    importStmts :: [LocAnn ImportStatement],
    -- | The main statements within the file.
    mainStmts :: [MainStatement [String]]
  }
  deriving Eq

-- | Displays an identifier by combining the 
-- qualifiers with full stops.
showName :: [String] -> String 
showName = intercalate "."

instance Show x => Show (Expr x) where 
  show Set = "Set"
  show Prop = "Prop"
  show (Type n) = "Type(" <> show n <> ")"
  show (Identifier x) = show x
  show (Forall x t e)
    = unwords ["forall", show x, ":", show t, ",", show e]
  show (Abs x t e) 
    = unwords ["fun", show x, ":", show t, "=>", show e]
  show (Let x t v e) 
    = unwords ["let", show x, ":", show t, "=", show v, "in", show e]
  show (App x e) = unwords ["(", show x, ")", "(", show e, ")"] 

instance Show x => Show (LocAnn x) where 
  show = show . annVal
  -- show (LocAnn pst off _ x) 
  --   = "(" <> sourcePosPretty sourcePos <> ")" <> "[" <> show x <> "]"
  --   where sourcePos = pstateSourcePos . snd $ reachOffset off pst


instance Show x => Show (MainStatement x) where
  show (Assume x expr) = unwords [show x, ":", show expr] 
  show (Define x Nothing expr) = unwords [show x, "=", show expr] 
  show (Define x (Just v) expr)
    = unwords [show x, ":", show v, "=", show expr] 
  
instance Show ImportStatement where 
  show (Import mn []) 
    = unwords ["import", show mn]
  show (Import mn xs) 
    = unwords ["import", show mn, "as", show xs]


instance Show FileContents where
  show (FileContents fn importStmts mainStmts) =
    unlines
      ( [unwords ["module", show fn, "where"]]
          <> [""]
          <> (show <$> importStmts)
          <> [""]
          <> (show <$> mainStmts)
      )
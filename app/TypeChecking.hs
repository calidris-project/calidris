{-|
Module      : TypeChecking
Description : Type checker for language
Copyright   : (c) TrueBoxGuy, 2022
License     : MIT
Maintainer  : https://github.com/TrueBoxGuy
Stability   : experimental
Portability : portable

Ensures that terms defined in language are well-formed 
and match their type annotations.
-}
{-# LANGUAGE ViewPatterns #-}
module TypeChecking where 

import Control.Monad
import Data.Foldable
import Data.List
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Set as S

import Error 
import Resolver
import Syntax

-- | Type synonym for maps to expressions.
type ExprMap = Map Integer (Expr ResolvedName)

-- * Ordering statements

-- | Creates, if possible, an ordering of the 'MainStatement's such 
-- that no 'MainStatement' depends on a name not already defined. 
-- Throws 'TopologicalError' otherwise.
topologicalSort 
    :: [MainStatement ResolvedName] 
    -> Either CustomBundle [MainStatement ResolvedName]
topologicalSort = go . lenSort . fmap (\x -> (dependencies x, x))
    where 
        isUniqueName (UniqueName _) = True
        isUniqueName _ = False
        extractNames (Assume _ t) = toList t
        extractNames (Define _ t e) = (toList t >>= toList) <> toList e
        lenSort = sortOn (S.size . fst)
        dependencies = S.fromList . filter isUniqueName . extractNames
        removeName stmt (s, x) = (S.delete (extractDef stmt) s, x) 
        go [] = pure [] 
        go ((s, stmt) : xs) | null s 
          = (stmt :) <$> go (lenSort $ removeName stmt <$> xs)
        go ((_, n) : xs) = 
          Left (mkBundleError TopologicalError (extractAnnDef n))

-- * Normalisation of the lambda calculus

-- | Increases an index by a shift if its value 
-- is greater than or equal to a given index index. 
applyShift 
    :: Integer -- ^ The level at which the shift starts.
    -> Integer -- ^ The shift to apply. 
    -> ResolvedName 
    -> ResolvedName
applyShift d s (Index i) | i >= d = Index (i + s)
applyShift _ _ x = x

-- | Calculates the application @(fun x : T => u) a@, 
-- by decrementing all indices greater in level than the binding x, 
-- and replacing the binding x with the term a, with the bound levels 
-- within this term being increased as appropriate.
replaceLvl 
  :: Integer 
    -- ^ The shift to apply to bound terms within the replacement term. 
    -- This is determined by the number of additional bindings that come before
    -- the term. 
  -> Integer 
    -- ^ The level of the binding @x@. 
  -> Expr ResolvedName 
    -- ^ The replacement term @a@. 
  -> Expr ResolvedName 
    -- ^ The term @u@. 
  -> Expr ResolvedName
replaceLvl s d v (Identifier (annVal -> Index i)) | i == d = applyShift d s <$> v
replaceLvl s d _ v@(Identifier (annVal -> Index i)) | i > d = Index (i - 1) <$ v
replaceLvl s d v (Forall x t e) = Forall x (replaceLvl s d v t) (replaceLvl (s + 1) d v e)
replaceLvl s d v (Abs x t e) = Abs x (replaceLvl s d v t) (replaceLvl (s + 1) d v e)
replaceLvl s d v (Let x t e1 e2) =
  Let
    x (replaceLvl s d v <$> t) (replaceLvl s d v e1) (replaceLvl (s + 1) d v e2)
replaceLvl s d v (App e1 e2) = App (replaceLvl s d v e1) (replaceLvl s d v e2)
replaceLvl s d v x = x

-- | Calculates the normal form of an expression.  
normaliseExpr 
  :: Integer 
    -- ^ The current depth of the expression. This is the level which would be given 
    -- to a new binding in the subexpression.
  -> ExprMap
    -- ^ A mapping from the unique integer given to a global name to
    -- the expression for that name. 
  -> Expr ResolvedName 
    -- The expression or subexpression being reduced.
  -> Expr ResolvedName
normaliseExpr d g (Identifier (annVal -> UniqueName u))
  | Just v <- M.lookup u g = applyShift 0 d <$> v
normaliseExpr d g (Forall x t e) =
  Forall x (normaliseExpr d g t) (normaliseExpr (d + 1) g e)
normaliseExpr d g (Abs x t e) =
  Abs x (normaliseExpr d g t) (normaliseExpr (d + 1) g e)
normaliseExpr d g (Let _ _ v e) = 
  normaliseExpr d g (replaceLvl 0 d v e)
normaliseExpr d g (App (Abs _ _ e) v) = normaliseExpr d g (replaceLvl 0 d v e) 
normaliseExpr d g (App a b) =
  let norm = normaliseExpr d g; a' = norm a; b' = norm b in 
      if a' /= a || b' /= b then norm (App a' b') else App a' b'  
normaliseExpr _ _ x = x

-- * Type checking

-- | Determines whether an expression is a sort. 
isSort :: Expr x -> Bool 
isSort Set = True 
isSort Prop = True 
isSort (Type _) = True
isSort _ = False

-- | Determines whether two expressions are equal when
-- location annotations are removed.
areEqual :: Expr ResolvedName -> Expr ResolvedName -> Bool
areEqual Set Set = True 
areEqual Prop Prop = True 
areEqual (Type i1) (Type i2) = i1 == i2 
areEqual (Identifier (annVal -> v1)) (Identifier (annVal -> v2)) = v1 == v2
areEqual (Forall _ t1 e1) (Forall _ t2 e2) = areEqual t1 t2 && areEqual e1 e2 
areEqual (Abs _ t1 e1) (Abs _ t2 e2) = areEqual t1 t2 && areEqual e1 e2
areEqual (Let _ t1 v1 e1) (Let _ t2 v2 e2)
    = liftEqual t1 t2 && areEqual v1 v2 && areEqual e1 e2
    where 
        liftEqual Nothing Nothing = True 
        liftEqual (Just t1) (Just t2) = areEqual t1 t2 
        liftEqual a b = False
areEqual (App a1 b1) (App a2 b2)
    = areEqual a1 a2 && areEqual b1 b2
areEqual _ _ = False

-- | Determines whether two expressions are equal 
-- up to eta expansion.
areEtaEqual 
    :: Integer -- ^ The depth at which the comparison is being done.
    -> Expr ResolvedName 
    -> Expr ResolvedName
    -> Bool
areEtaEqual d v1@(Abs _ _ e) v2
    =  areEqual v1 v2 
    || areEtaEqual (d + 1) e (App v2 (Identifier (NoLoc $ Index d)))
areEtaEqual d v1 v2@(Abs _ _ e)
    =  areEqual v1 v2 
    || areEtaEqual (d + 1) e (App v1 (Identifier (NoLoc $ Index d)))
areEtaEqual _ v1 v2 = areEqual v1 v2

-- | Determines whether an expression is convertible to 
-- another according to the subtyping relationship. 
isConvertible :: Expr ResolvedName -> Expr ResolvedName -> Bool
isConvertible v1 v2 | areEqual v1 v2 = True
isConvertible Prop Set = True 
isConvertible Prop (Type _) = True 
isConvertible Set (Type _) = True 
isConvertible (Type a) (Type b) = a <= b
isConvertible (Forall _ t1 e1) (Forall _ t2 e2)
    = areEqual t1 t2 && isConvertible e1 e2 
isConvertible _ _ = False 

-- | Guards on the convertibility of two expressions.
checkConvertible 
    :: LocAnn x
    -> Integer
    -> ExprMap
      -- ^ A mapping from the unique integer given to a global name to
      -- the expression for that name. 
    -> Expr ResolvedName
    -> Expr ResolvedName
    -> Either CustomBundle ()
checkConvertible p d g a b 
    = case isConvertible (normaliseExpr d g a) (normaliseExpr d g b) of 
        True -> pure () 
        False -> Left (mkBundleError TypeError p)

-- | Forms a type for an expression or subexpression. 
formType 
    :: LocAnn x
    -> Integer -- ^ The subexpression depth.
    -> ExprMap
        -- ^ A mapping from De Bruijn levels to the type of that binding. 
    -> ExprMap
        -- ^ A mapping from the unique integer for each 
        -- global name to the value of that expression.
    -> ExprMap
        -- ^ A mapping from the unique integer for each 
        -- global name to the type of that expression. 
    -> Expr ResolvedName
    -> Either CustomBundle (Expr ResolvedName)
formType p _ _ _ _ Prop = pure $ Type 0 
formType p _ _ _ _ Set = pure $ Type 0 
formType p _ _ _ _ (Type i) = pure $ Type (i + 1)
formType p d _ _ typeMap (Identifier (annVal -> UniqueName u))
    | Just t <- M.lookup u typeMap = pure (applyShift 0 d <$> t)
formType p d l _ _ (Identifier (annVal -> Index i))
    | Just t <- M.lookup i l = pure (applyShift i (d - i) <$> t)
formType p d l valMap typeMap (Forall _ t e) = do
  tt <- normaliseExpr d valMap <$> formType p d l valMap typeMap t
  te <-
    normaliseExpr (d + 1) valMap <$> formType p (d + 1) (M.insert d t l) valMap typeMap e
  case (tt, te) of 
    (x, Prop) | isSort x -> pure Prop 
    (x, Set) | x == Set || x == Prop -> pure Set 
    (x, y) | isSort x && isSort y -> let lvl (Type i) = i; lvl _ = 0 in 
      pure $ Type (max (lvl x) (lvl y))
    _ -> Left (mkBundleError TypeError p)
formType p d l valMap typeMap (Abs x t e) = do 
    te <- formType p (d + 1) (M.insert d t l) valMap typeMap e
    let finT = Forall x t te
    formType p d l valMap typeMap finT 
    pure finT 
formType p d l valMap typeMap (App a b) = do 
    tb <- formType p d l valMap typeMap b 
    ta <- normaliseExpr d valMap <$> formType p d l valMap typeMap a
    case ta of 
        Forall _ t e -> do 
            checkConvertible p d valMap tb t 
            pure $ replaceLvl 0 d b e
        _ -> Left (mkBundleError TypeError p) 
formType p d l valMap typeMap (Let p2 t v e) = do
    tv <- formType p2 d l valMap typeMap v 
    traverse_ (checkConvertible p2 d valMap tv) t
    formType p d l valMap typeMap (replaceLvl 0 d v e)
formType p _ _ _ _ _ = Left (mkBundleError TypeError p)

-- | Introduces each statement into the global context according to the rules 
-- for well-founded global contexts. 
introTypes :: [MainStatement ResolvedName] -> Either CustomBundle (ExprMap, ExprMap)
introTypes = foldM introStmt (M.empty, M.empty)
    where 
        introStmt (typeMap, valMap) (Assume ann@(annVal -> UniqueName i) t)
            = do 
                tt <- normaliseExpr 0 valMap 
                    <$> formType ann 0 mempty valMap typeMap t
                if isSort tt then  pure (M.insert i t typeMap, valMap) 
                    else Left (mkBundleError TypeError ann)
        introStmt (typeMap, valMap) (Define ann@(annVal -> UniqueName i) t v)
            = do 
                tt <- formType ann 0 mempty valMap typeMap v 
                case t of 
                    Nothing -> pure ()
                    Just t1 -> checkConvertible ann 0 valMap tt t1 
                pure (M.insert i tt typeMap, M.insert i v valMap)
        introStmt _ _ = error "ex falso quodlibet (the impossible happened)"

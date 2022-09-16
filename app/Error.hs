{-|
Module      : Error
Description : Error types for language processing
Copyright   : (c) TrueBoxGuy, 2022
License     : MIT
Maintainer  : https://github.com/TrueBoxGuy
Stability   : experimental
Portability : portable

Types for errors that may be thrown when processing the
user input. Enables for pretty display of errors using 
'ParseErrorBundle'.
-}
module Error where 

import Data.List
import qualified Data.Set as S
import Text.Megaparsec

import Syntax

-- | 'ParseErrorBundle' instantiated with the custom 
-- type 'Error'. 
type CustomBundle = ParseErrorBundle String Error

-- | Types of errors that may be thrown.
data ErrorType
    = ReservedError [String] 
      -- ^ Error for user trying to define a reserved name. 
    | ModuleDuplicationError [String]
      -- ^ Error for user defining a module multiple times. 
    | FindModuleError [String]
      -- ^ Error for when a module can not be found. 
    | UndefinedError
      -- ^ Error for when a name is undefined. 
    | ShadowingError [String]
      -- ^ Error for when an expression reintroduces a name. 
    | TopologicalError 
      -- ^ Error for when a topological sort is impossible.
    | TypeError 
      -- ^ Error for when a valid type could not be deduced for 
      -- a declaration.
    deriving (Eq, Ord)

-- | An 'ErrorType' alongside associated information. 
data Error = Error
  { errType :: ErrorType,
    -- | The length of the parsed item for which
    -- the error is being thrown, which is used for pretty printing.
    errLen :: Int
  }
  deriving (Eq, Ord)

-- | Makes a 'ParseError'. 
mkParseError 
  :: ErrorType 
  -> LocAnn x -- ^ The location where the error resides. 
  -> ParseError String Error
mkParseError eType (LocAnn _ off len _)
  = FancyError off (S.singleton (ErrorCustom $ Error eType len))
mkParseError _ _ = error "Error thrown for internal binding"

-- | Makes a 'CustomBundle'.
mkBundleError 
  :: ErrorType
  -> LocAnn x -- ^ The location where the error resides. 
  -> CustomBundle
mkBundleError cons ann@(LocAnn posState _ _ _)
  = ParseErrorBundle (pure $ mkParseError cons ann) posState
mkBundleError _ _ = error "Error thrown for internal binding"

instance ShowErrorComponent Error where 
  showErrorComponent (Error (ReservedError n) _)
    = "the name " <> showName n <> " is reserved"
  showErrorComponent (Error (ModuleDuplicationError n) _)
    = "the module " <> showName n <> " has already been defined"
  showErrorComponent (Error (FindModuleError n) _)
    = "could not find module " <> showName n
  showErrorComponent (Error UndefinedError _)
    = "name is undefined"
  showErrorComponent (Error (ShadowingError n) _)
    = "the name " 
    <> showName n <> " can not be redefined"
  showErrorComponent (Error TopologicalError _)
    = "could not form type for name owing to cyclic dependencies"
  showErrorComponent (Error TypeError _)
    = "could not deduce valid type for name"
  errorComponentLen (Error _ l) = l 
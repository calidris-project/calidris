module Main where

import Control.Monad.Except 
import Data.Foldable
import System.IO
import Text.Megaparsec


import Parser
import Resolver 
import TypeChecking
import Syntax

main :: IO ()
main = do
    -- putStr "Folder name: "
    -- hFlush stdout
    -- dir <- getLine 
    let dir = "Working"
    res <- runExceptT (input dir >>= liftEither . (toMainStatements >=> topologicalSort >=> introTypes) )
    either (putStrLn . errorBundlePretty) (pure $ putStrLn "All definitions accepted") res

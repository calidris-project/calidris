{-|
Module      : Parser
Description : Parser for language
Copyright   : (c) TrueBoxGuy, 2022
License     : MIT
Maintainer  : https://github.com/TrueBoxGuy
Stability   : experimental
Portability : portable

Parsers that are ultimately used to form a 
list of 'FileContents' from a directory.
-}
module Parser where

import qualified Control.Exception as E
import Control.Monad.Except
import Data.Bifunctor
import Data.Foldable
import Data.List
import Data.Maybe
import System.Directory
import System.FilePath
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L


import Error
import Paths_Calidris
import Syntax

-- | The type used for the language parser.
type Parser = Parsec Error String

spaceConsumer, spaceConsumer' :: Parser () 
-- | Consumes whitespace, line comments beginning with @--@, 
-- and block comments, which have start indicated by @{-@
-- and end indicated by @-}@.
spaceConsumer 
  = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")
-- | Consumes horizontal whitespace, line comments beginning with @--@, 
-- and block comments, which have start indicated by @{-@
-- and end indicated by @-}@.
spaceConsumer' 
  = L.space hspace1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}") 


lexeme, lexeme', lexemeS :: Parser a -> Parser a 
-- | Consumes whitespace using 'spaceConsumer' after running a parser.
lexeme = L.lexeme spaceConsumer
-- | Consumes whitespace using 'spaceConsumer\'' after running a parser.
lexeme' = L.lexeme spaceConsumer' 
-- | Run a parser and then consume whitespace using 'spaceConsumer'.
-- Also ensures that the string is followed by either whitespace, 
-- or one of the characters ",:;=()". 
lexemeS = lexeme . try . (<* lookAhead (space1 <|> void (oneOf ",:;=()"))) 

symbol, symbol', symbolS :: String -> Parser String
-- | Parses a string and then consume whitespace using 'spaceConsumer'. 
symbol = L.symbol spaceConsumer
-- | Parses a string and then consume whitespace using 'spaceConsumer\''. 
symbol' = L.symbol spaceConsumer'
-- | Parses a string using 'lexemeS'. 
symbolS = lexemeS . string

-- | Annotates a parsed value with 'LocAnn'. 
errAnn :: Parser x -> Parser (LocAnn x)
errAnn parser = do 
  state1 <- getParserState
  let firstOffset = stateOffset state1
  parsed <- parser 
  diff <- (- firstOffset +) . stateOffset <$> getParserState
  pure (LocAnn (statePosState state1) firstOffset diff parsed)

-- | Names which can not be defined within the language. 
reservedIdentifiers :: [[String]]
reservedIdentifiers = pure <$> 
  [ "forall", "let", "in", "fun", "Set", "Prop",
    "Type", "import", "as", "module", "where"
  ]

-- | Parses an identifier, which consists of a list of strings
-- (consisting of characters that are either alphanumeric or one of @_+*/-~$!@) 
-- of length at least 1, and also ensures this identifier is not reserved. 
identifierParser :: Parser (LocAnn [String])
identifierParser = do
  symb <- errAnn $ some (alphaNumChar <|> oneOf "_+*/-~$!@") `sepBy1` char '.'
  if annVal symb `elem` reservedIdentifiers
    then
      parseError $ mkParseError (ReservedError (annVal symb)) symb 
    else pure symb

-- | 'identifierParser\'' without an annotation. 
identifierParser' :: Parser [String]
identifierParser' = annVal <$> identifierParser

-- | Parses expressions within the language, with the exception 
-- of top level applications. Such expressions are parsed separately 
-- to ensure left associativity. 
expressionParser1 :: Parser (Expr [String])
expressionParser1
    = asum [
      Set <$ symbolS "Set", 
      Prop <$ symbolS "Prop", 
      Type <$> lexemeS (symbol "Type(" *> L.decimal <* char ')'), 
      Forall
        <$> (symbolS "forall" *> lexeme identifierParser)
        <*> (symbol ":" *> expressionParser)
        <*> (symbol "," *> expressionParser), 
       Abs
        <$> (symbolS "fun" *> lexeme identifierParser)
        <*> (symbol ":" *> expressionParser)
        <*> (symbol "=>" *> expressionParser), 
       Let
        <$> (symbolS "let" *> lexeme identifierParser)
        <*> optional (symbol ":" *> expressionParser)
        <*> (symbol "=" *> expressionParser)
        <*> (symbolS "in" *> expressionParser),
       try $ Identifier <$> lexeme identifierParser, 
       between (symbol "(") (symbol ")") expressionParser
    ]

-- | Parses top level applications and combines them 
-- in a left recursive manner. 
expressionParser :: Parser (Expr [String])
expressionParser = foldl1 App <$> some expressionParser1

-- | Parses a declaration of the module name.
moduleNameParser :: Parser [String] 
moduleNameParser 
  = symbol' "module" *> lexeme' identifierParser' <* symbol "where"

-- | Parses an import statement, which is either of the form 
-- @import module as qualifier@ or @import module@.
importParser :: Parser ImportStatement
importParser 
  = Import 
  <$> (symbol' "import" *> lexeme' identifierParser') 
  <*> lexeme (fromMaybe [] <$> optional (symbol' "as" *> identifierParser'))

-- | Parses the main statements within a file. 
-- All assumptions are of the form @x : T@, with 
-- definitions being either of the form @x = e@
-- or @x : T = e@.
mainStatementParser :: Parser (MainStatement [String])
mainStatementParser =
  ( try
      ( typedConv
          <$> lexeme identifierParser
          <*> (symbol ":" *> expressionParser)
          <*> optional (symbol "=" *> expressionParser)
      )
      <|> ( untypedConv
              <$> lexeme identifierParser
              <*> (symbol "=" *> expressionParser)
          )
  )
    <* symbol ";"
  where
    typedConv v t Nothing = Assume v t
    typedConv v t (Just d) = Define v (Just t) d
    untypedConv v d = Define v Nothing d

-- | Parses the module name, import statements, and main statements 
-- within a file. 
fileContentsParser :: Parser FileContents
fileContentsParser =
  FileContents
    <$> errAnn moduleNameParser 
    <*> many (errAnn importParser)
    <*> many mainStatementParser <* eof

-- | Give names of files in a directory (relative to that directory)
-- in the data directory. All names are given relative to this root
-- directory, and the presence of symbolic links within
-- this root directory will lead to an error being thrown. 
getFiles :: String -> IO [String]
getFiles rootPath = do
  dataPath <- getDataDir
  filenames <- listDirectory (dataPath </> rootPath)
  let fileFolderCase fn = do
        isSymLink <- pathIsSymbolicLink (dataPath </> rootPath </> fn)
        if isSymLink
          then fail "symbolic link is present in data directory" 
          else pure ()
        isDir <- doesDirectoryExist (dataPath </> rootPath </> fn)
        if isDir
          then fmap (combine fn) <$> getFiles (rootPath </> fn)
          else pure [fn]
  concat <$> traverse fileFolderCase filenames

-- | Parses all the file contents within a root directory 
-- within the data directory. 
input :: String -> ExceptT CustomBundle IO [FileContents]
input dir = do
  dataPath <- liftIO getDataDir
  filenames <- liftIO $ getFiles dir
  traverse
    ( \fn -> do
        file <- liftIO . readFile $ dataPath </> dir </> fn
        liftEither $ parse fileContentsParser fn file
    )
    filenames

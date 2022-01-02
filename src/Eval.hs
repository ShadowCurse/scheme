{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Eval
  (
  evalText
  , evalFile
  , runParseTest
  , safeExec
  -- testing
  -- , runASTinEnv
  -- , basicEnv
  -- , fileToEvalForm
  -- , textToEvalForm
  -- , getFileContents
  ) where

import LispVal
  ( EnvCtx(..)
  , Eval(unEval)
  , IFunc(IFunc)
  , LispException(Default, PError, UnboundVar, TypeMismatch,
                    BadSpecialForm, NotFunction)
  , LispVal(..)
  , showVal
  )
import Parser (readExpr, readExprFile)

import Data.Map as Map
  ( Map
  , empty
  , fromList
  , insert
  , lookup
  , partition
  , toList
  , union
  )
import qualified Data.Text as T
import qualified Data.Text.IO as TIO

import Prim (primEnv, unop)
import Text.Parsec (ParseError)

import Control.Exception (Exception(fromException), SomeException, throw, try)
import Control.Monad.Reader
  ( MonadIO(liftIO)
  , MonadReader(ask, local)
  , ReaderT(runReaderT)
  , asks
  )
import System.Directory ( doesFileExist )

basicEnv :: Map.Map T.Text LispVal
basicEnv = Map.fromList $ primEnv <> [("read", Fun $ IFunc $ unop $ readFn)]

readFn :: LispVal -> Eval LispVal
readFn (String txt) = lineToEvalForm txt
readFn val = throw $ TypeMismatch "read expects string, instead got: " val

parseFn :: LispVal -> Eval LispVal
parseFn (String txt) = either (throw . PError . show) return $ readExpr txt
parseFn val = throw $ TypeMismatch "parse expects sting, instead got: " val

lineToEvalForm :: T.Text -> Eval LispVal
lineToEvalForm input = either (throw . PError . show) eval $ readExpr input

evalFile :: T.Text -> IO ()
evalFile fileExpr = (runASTinEnv basicEnv $ fileToEvalForm fileExpr) >>= print

fileToEvalForm :: T.Text -> Eval LispVal
fileToEvalForm input =
  either (throw . PError . show) evalBody $ readExprFile input

-- endOfList :: LispVal -> LispVal -> LispVal
-- endOfList (List x) expr = List $ x ++ [expr]
-- endOfList n _  = throw $ TypeMismatch  "failure to get variable: " n

-- parseWithLib :: T.Text -> T.Text -> Either ParseError LispVal
parseWithLib :: T.Text -> Either ParseError LispVal
parseWithLib inp = do
  -- stdlib <- readExprFile sTDLIB std
  expr   <- readExpr inp
  return $ expr -- endOfList stdlib expr

-- getFileContents :: FilePath -> IO T.Text
-- getFileContents fname = do
--   exists <- doesFileExist fname
--   if exists then TIO.readFile  fname else return "File does not exist."

-- textToEvalForm :: T.Text -> T.Text -> Eval LispVal
textToEvalForm :: T.Text -> Eval LispVal
textToEvalForm input = either (throw . PError . show ) evalBody $ parseWithLib input

evalText :: T.Text -> IO () --REPL
evalText textExpr = do
  -- stdlib <- getFileContents sTDLIB
  -- stdlib <- T.pack ""
  res <- runASTinEnv basicEnv $ textToEvalForm textExpr
  print res

runParseTest :: T.Text -> T.Text -- for view AST
runParseTest input = either (T.pack . show) (T.pack . show) $ readExpr input

runASTinEnv :: EnvCtx -> Eval b -> IO b
runASTinEnv code action = runReaderT (unEval action) code

getVar :: LispVal -> Eval LispVal
getVar (Atom atom) = do
  env <- ask
  case Map.lookup atom env of
    Just x -> return x
    Nothing -> throw $ UnboundVar atom
getVar n = throw $ TypeMismatch  "failure to get variable: " n

getEven :: [t] -> [t]
getEven [] = []
getEven (x:xs) = x : getOdd xs

getOdd :: [t] -> [t]
getOdd [] = []
getOdd (x:xs) = x : getEven xs

ensureAtom :: LispVal -> Eval LispVal
ensureAtom n@(Atom _) = return n
ensureAtom n = throw $ TypeMismatch "atom" n

extractVar :: LispVal -> T.Text
extractVar (Atom atom) = atom

evalBody :: LispVal -> Eval LispVal
evalBody (List [List ((:) (Atom "define") [Atom var, defExpr]), rest]) = do
  evalVal <- eval defExpr
  env <- ask
  local (const $ Map.insert var evalVal env) $ eval rest
evalBody (List ((:) (List ((:) (Atom "define") [Atom var, defExpr])) rest)) = do
  evalVal <- eval defExpr
  env <- ask
  let envFn = const $ Map.insert var evalVal env
   in local envFn $ evalBody $ List rest
evalBody x = eval x

applyLambda :: LispVal -> [LispVal] -> [LispVal] -> Eval LispVal
applyLambda expr params args = do
  env <- ask
  argEval <- mapM eval args
  let env' =
        Map.fromList
          (Prelude.zipWith (\a b -> (extractVar a, b)) params argEval) <>
        env
   in local (const env') $ eval expr

safeExec :: IO a -> IO (Either String a)
safeExec m = do
  result <- Control.Exception.try m
  case result of
    Left (eTop :: SomeException) ->
      case fromException eTop of
        Just (enclosed :: LispException) -> return $ Left (show enclosed)
        Nothing -> return $ Left (show eTop)
    Right val -> return $ Right val

eval :: LispVal -> Eval LispVal
eval (List [Atom "quote", val]) = return val
eval (Number i) = return $ Number i
eval (String i) = return $ String i
eval (Bool i) = return $ Bool i
eval (List i) = return Nil
eval Nil = return Nil
eval (List [Atom "write", rest]) = return . String . T.pack $ show rest
eval (List ((:) (Atom "write") rest)) =
  return . String . T.pack . show $ List rest
eval n@(Atom _) = getVar n
eval (List [Atom "if", pred, truExpr, flsExpr]) = do
  ifRes <- eval pred
  case ifRes of
    (Bool True) -> eval truExpr
    (Bool False) -> eval flsExpr
    _ -> throw $ BadSpecialForm "if"
eval (List [Atom "let", List pairs, expr]) = do
  env <- ask
  atoms <- mapM ensureAtom $ getEven pairs
  vals <- mapM eval $ getOdd pairs
  let env' =
        Map.fromList (Prelude.zipWith (\a b -> (extractVar a, b)) atoms vals) <>
        env
   in local (const env') $ evalBody expr
eval (List [Atom "begin", rest]) = evalBody rest
eval (List ((:) (Atom "begin") rest)) = evalBody $ List rest
eval (List [Atom "define", varExpr, expr]) = do
  varAtom <- ensureAtom varExpr
  evalVal <- eval expr
  env <- ask
  let envFn = const $ Map.insert (extractVar varAtom) evalVal env
   in local envFn $ return varExpr
eval (List [Atom "lambda", List params, expr]) = do
  envLocal <- ask
  return $ Lambda (IFunc $ applyLambda expr params) envLocal
eval (List (Atom "lambda":_)) = throw $ BadSpecialForm "lambda"
eval (List ((:) x xs)) = do
  funVar <- eval x
  xVal <- mapM eval xs
  case funVar of
    (Fun (IFunc internalFn)) -> internalFn xVal
    (Lambda (IFunc internalfn) boundenv) ->
      local (const boundenv) $ internalfn xVal
    _ -> throw $ NotFunction funVar

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards #-}

module Eval
  ( evalText
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
  , LispException(BadSpecialForm, Default, NotFunction, PError,
              TypeMismatch, UnboundVar)
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
import System.Directory (doesFileExist)

sTDLIB :: FilePath
sTDLIB = "lib/stdlib.scm"

funcEnv :: Map.Map T.Text LispVal
funcEnv =
  Map.fromList $
  primEnv <>
  [ ("read", Fun $ IFunc $ unop readFn)
  , ("parse", Fun $ IFunc $ unop parseFn)
  , ("eval", Fun $ IFunc $ unop eval)
  , ("show", Fun $ IFunc $ unop (return . String . showVal))
  ]

basicEnv :: EnvCtx
basicEnv = EnvCtx Map.empty funcEnv

updateEnv :: T.Text -> LispVal -> EnvCtx -> EnvCtx
updateEnv var e@(Fun _) EnvCtx {..} = EnvCtx env $ Map.insert var e fenv
updateEnv var e@(Lambda _ _) EnvCtx {..} = EnvCtx env $ Map.insert var e fenv
updateEnv var e EnvCtx {..} = EnvCtx (Map.insert var e env) fenv

appendToList :: LispVal -> LispVal -> LispVal
appendToList (List x) expr = List $ x ++ [expr]
appendToList n _ = throw $ TypeMismatch "failure to get variable: " n

getFileContents :: FilePath -> IO T.Text
getFileContents fname = do
  exists <- doesFileExist fname
  if exists
    then TIO.readFile fname
    else return "File does not exist."

combineWithStdLib :: T.Text -> T.Text -> Either ParseError LispVal
combineWithStdLib std input = do
  stdlib <- readExprFile std
  expr <- readExpr input
  return $ appendToList stdlib expr

lineToEvalForm :: T.Text -> Eval LispVal
lineToEvalForm input = either (throw . PError . show) eval $ readExpr input

textToEvalForm :: T.Text -> T.Text -> Eval LispVal
textToEvalForm std input =
  either (throw . PError . show) evalBody $ combineWithStdLib std input

fileToEvalForm :: T.Text -> Eval LispVal
fileToEvalForm input =
  either (throw . PError . show) evalBody $ readExprFile input

readFn :: LispVal -> Eval LispVal
readFn (String txt) = lineToEvalForm txt
readFn val = throw $ TypeMismatch "read expects string, instead got: " val

parseFn :: LispVal -> Eval LispVal
parseFn (String txt) = either (throw . PError . show) return $ readExpr txt
parseFn val = throw $ TypeMismatch "parse expects sting, instead got: " val

evalText :: T.Text -> IO () --REPL
evalText textExpr = do
  stdlib <- getFileContents sTDLIB
  res <- runASTinEnv basicEnv (textToEvalForm stdlib textExpr)
  print res

evalFile :: T.Text -> IO ()
evalFile fileExpr = runASTinEnv basicEnv (fileToEvalForm fileExpr) >>= print

runParseTest :: T.Text -> T.Text -- for view AST
runParseTest input = either (T.pack . show) (T.pack . show) $ readExpr input

runASTinEnv :: EnvCtx -> Eval b -> IO b
runASTinEnv env code = runReaderT (unEval code) env

getVar :: LispVal -> Eval LispVal
getVar (Atom atom) = do
  EnvCtx {..} <- ask
  case Map.lookup atom (Map.union fenv env) of
    Just x -> return x
    Nothing -> throw $ UnboundVar atom
getVar n = throw $ TypeMismatch "failure to get variable: " n

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

isLambda :: LispVal -> Bool
isLambda (List ((Atom "lambda"):_)) = True
isLambda _ = False

applyLambda :: LispVal -> [LispVal] -> [LispVal] -> Eval LispVal
applyLambda expr params args = bindArgsEval params args expr

safeExec :: IO a -> IO (Either String a)
safeExec m = do
  result <- Control.Exception.try m
  case result of
    Left (eTop :: SomeException) ->
      case fromException eTop of
        Just (enclosed :: LispException) -> return $ Left (show enclosed)
        Nothing -> return $ Left (show eTop)
    Right val -> return $ Right val

bindArgsEval :: [LispVal] -> [LispVal] -> LispVal -> Eval LispVal
bindArgsEval params args expr = do
  EnvCtx {..} <- ask
  let newVars = zipWith (\a b -> (extractVar a, b)) params args
  let (newEnv, newFenv) = Map.partition (not . isLambda) $ Map.fromList newVars
  local (const $ EnvCtx (newEnv <> env) (newFenv <> fenv)) $ eval expr

evalBody :: LispVal -> Eval LispVal
evalBody (List [List ((:) (Atom "define") [Atom var, defExpr]), rest]) = do
  evalVal <- eval defExpr
  ctx <- ask
  local (const $ updateEnv var evalVal ctx) $ eval rest
evalBody (List ((:) (List ((:) (Atom "define") [Atom var, defExpr])) rest)) = do
  evalVal <- eval defExpr
  ctx <- ask
  local (const $ updateEnv var evalVal ctx) $ evalBody $ List rest
evalBody x = eval x

eval :: LispVal -> Eval LispVal
eval (List [Atom "quote", val]) = return val
eval (Number i) = return $ Number i
eval (String s) = return $ String s
eval (Bool b) = return $ Bool b
eval (List []) = return Nil
eval Nil = return Nil
eval n@(Atom _) = getVar n
eval (List [Atom "write", rest]) = return . String . T.pack $ show rest
eval (List ((:) (Atom "write") rest)) =
  return . String . T.pack . show $ List rest
eval (List [Atom "if", pred, trueExpr, falseExpr]) = do
  ifRes <- eval pred
  case ifRes of
    (Bool True) -> eval trueExpr
    (Bool False) -> eval falseExpr
    _ -> throw $ BadSpecialForm "if"
eval (List ((:) (Atom "if") _)) =
  throw $ BadSpecialForm "(if <bool> <s-expr> <s-expr>)"
eval (List [Atom "let", List pairs, expr]) = do
  EnvCtx {} <- ask
  atoms <- mapM ensureAtom $ getEven pairs
  vals <- mapM eval $ getOdd pairs
  bindArgsEval atoms vals expr
eval (List (Atom "let":_)) =
  throw $
  BadSpecialForm
    "let function expects list of parameters and S-Expression body\n(let <pairs> <s-expr>)"
eval (List [Atom "begin", rest]) = evalBody rest
eval (List ((:) (Atom "begin") rest)) = evalBody $ List rest
eval (List [Atom "define", varExpr, defExpr]) --top-level define
 = do
  EnvCtx {} <- ask
  _varAtom <- ensureAtom varExpr
  _evalVal <- eval defExpr
  bindArgsEval [varExpr] [defExpr] varExpr
eval (List [Atom "lambda", List params, expr]) = do
  asks (Lambda (IFunc $ applyLambda expr params))
eval (List (Atom "lambda":_)) =
  throw $
  BadSpecialForm
    "lambda function expects list of parameters and S-Expression body\n(lambda <params> <s-expr>)"
eval (List ((:) x xs)) = do
  EnvCtx {..} <- ask
  funVar <- eval x
  xVal <- mapM eval xs
  case funVar of
    (Fun (IFunc internalFn)) -> internalFn xVal
    (Lambda (IFunc definedFn) (EnvCtx benv _bfenv)) ->
      local (const $ EnvCtx benv fenv) $ definedFn xVal
    _ -> throw $ NotFunction funVar

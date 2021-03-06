{-# LANGUAGE OverloadedStrings #-}

module Prim
  ( primEnv
  , unop
  ) where

import LispVal
  ( Eval
  , IFunc(IFunc)
  , LispException(ExpectedList, IOError, NumArgs, TypeMismatch)
  , LispVal(Atom, Bool, Fun, List, Nil, Number, String)
  )

import Data.Functor ((<&>))
import Data.Text as T (Text, concat, pack, unpack)
import Data.Text.IO as TIO (hGetContents, hPutStr)

import System.Directory ( doesFileExist )
import System.IO (Handle, IOMode(ReadMode, WriteMode), hIsWritable, withFile)

import Control.Exception (throw)

import Network.HTTP ( getRequest, getResponseBody, simpleHTTP )
import Control.Monad.Except (MonadIO(liftIO), foldM)

type Prim = [(T.Text, LispVal)]

type Unary = LispVal -> Eval LispVal

type Binary = LispVal -> LispVal -> Eval LispVal

mkF :: ([LispVal] -> Eval LispVal) -> LispVal
mkF = Fun . IFunc

primEnv :: Prim
primEnv =
  [ ("+", mkF $ binopFold (numOp (+)) (Number 0))
  , ("*", mkF $ binopFold (numOp (*)) (Number 1))
  , ("++", mkF $ binopFold (strOp (<>)) (String ""))
  , ("-", mkF $ binop $ numOp (-))
  , ("<", mkF $ binop $ numCmp (<))
  , ("<=", mkF $ binop $ numCmp (<=))
  , (">", mkF $ binop $ numCmp (>))
  , (">=", mkF $ binop $ numCmp (>=))
  , ("==", mkF $ binop $ numCmp (==))
  , ("even?", mkF $ unop $ numBool even)
  , ("odd?", mkF $ unop $ numBool odd)
  , ("pos?", mkF $ unop $ numBool (< 0))
  , ("neg?", mkF $ unop $ numBool (> 0))
  , ("eq?", mkF $ binop eqCmd)
  , ("bl-eq?", mkF $ binop $ eqOp (==))
  , ("and", mkF $ binopFold (eqOp (&&)) (Bool True))
  , ("or", mkF $ binopFold (eqOp (||)) (Bool False))
  , ("cons", mkF Prim.cons)
  , ("cdr", mkF Prim.cdr)
  , ("car", mkF Prim.car)
  , ("file?", mkF $ unop fileExists)
  , ("slurp", mkF $ unop slurp)
  , ("wslurp", mkF $ unop wSlurp)
  , ("put"   , mkF $ binop put)
  ]

unop :: Unary -> [LispVal] -> Eval LispVal
unop op [x] = op x
unop _ args = throw $ NumArgs 1 args

binop :: Binary -> [LispVal] -> Eval LispVal
binop op [x, y] = op x y
binop _ args = throw $ NumArgs 2 args

binopFold :: Binary -> LispVal -> [LispVal] -> Eval LispVal
binopFold op farg args =
  case args of
    [a, b] -> op a b
    (a:as) -> foldM op farg args
    [] -> throw $ NumArgs 2 args

fileExists :: LispVal -> Eval LispVal
fileExists (Atom atom) = fileExists $ String atom
fileExists (String txt) = Bool <$> liftIO (doesFileExist $ T.unpack txt)
fileExists val = throw $ TypeMismatch "read expects string, got: " val

slurp :: LispVal -> Eval LispVal
slurp (String txt) = liftIO $ wFileSlurp txt
slurp val = throw $ TypeMismatch "expects str, got: " val

wFileSlurp :: T.Text -> IO LispVal
wFileSlurp fileName = withFile (T.unpack fileName) ReadMode go
  where
    go = readTextFile fileName

openURL :: T.Text -> IO LispVal
openURL x = do
  req <- simpleHTTP (getRequest $ T.unpack x)
  body <- getResponseBody req
  return $ String $ T.pack body

wSlurp :: LispVal -> Eval LispVal
wSlurp (String txt) = liftIO $ openURL txt
wSlurp val = throw $ TypeMismatch "wSlurp expects a string, instead got: " val

readTextFile :: T.Text -> Handle -> IO LispVal
readTextFile fileName handle = do
  exists <- doesFileExist $ T.unpack fileName
  if exists
    then (TIO.hGetContents handle) >>= (return . String)
    else throw $ IOError $ T.concat [" file does not exits: ", fileName]

put :: LispVal -> LispVal -> Eval LispVal
put (String file) (String msg) = liftIO $ wFilePut file msg
put (String _) val =
  throw $
  TypeMismatch
    "pudt expects sting in the second argument (try using show), instead got: "
    val
put val _ = throw $ TypeMismatch "put expects string, instead got: " val

wFilePut :: T.Text -> T.Text -> IO LispVal
wFilePut fileName msg = withFile (T.unpack fileName) WriteMode go
  where
    go = putTextFile fileName msg

putTextFile :: T.Text -> T.Text -> Handle -> IO LispVal
putTextFile fileName msg handle = do
  canWrite <- hIsWritable handle
  if canWrite
    then (TIO.hPutStr handle msg) >> (return $ String msg)
    else throw $ IOError $ T.concat [" file does not exist: ", fileName]

cons :: [LispVal] -> Eval LispVal
cons [x, y@(List yList)] = return $ List $ x : yList
cons [c] = return $ List [c]
cons [] = return $ List []
cons _ = throw $ ExpectedList "cons, in second argumnet"

car :: [LispVal] -> Eval LispVal
car [List []] = return Nil
car [List (x:_)] = return x
car [] = return Nil
car x = throw $ ExpectedList "car"

cdr :: [LispVal] -> Eval LispVal
cdr [List (x:xs)] = return $ List xs
cdr [List []] = return Nil
cdr [] = return Nil
cdr x = throw $ ExpectedList "cdr"

numBool :: (Integer -> Bool) -> LispVal -> Eval LispVal
numBool op (Number x) = return $ Bool $ op x
numBool op x = throw $ TypeMismatch "numeric op " x

numOp :: (Integer -> Integer -> Integer) -> LispVal -> LispVal -> Eval LispVal
numOp op (Number x) (Number y) = return $ Number $ op x y
numOp op x (Number y) = throw $ TypeMismatch "numeric op " x
numOp op (Number x) y = throw $ TypeMismatch "numeric op " y
numOp op x y = throw $ TypeMismatch "numeric op " x

strOp :: (T.Text -> T.Text -> T.Text) -> LispVal -> LispVal -> Eval LispVal
strOp op (String x) (String y) = return $ String $ op x y
strOp op x (String y) = throw $ TypeMismatch "string op " x
strOp op (String x) y = throw $ TypeMismatch "string op " y
strOp op x y = throw $ TypeMismatch "string op " x

eqOp :: (Bool -> Bool -> Bool) -> LispVal -> LispVal -> Eval LispVal
eqOp op (Bool x) (Bool y) = return $ Bool $ op x y
eqOp op x (Bool y) = throw $ TypeMismatch "bool op " x
eqOp op (Bool x) y = throw $ TypeMismatch "bool op " y
eqOp op x y = throw $ TypeMismatch "bool op " x

numCmp :: (Integer -> Integer -> Bool) -> LispVal -> LispVal -> Eval LispVal
numCmp op (Number x) (Number y) = return . Bool $ op x y
numCmp _ x (Number _) = throw $ TypeMismatch "numeric op " x
numCmp _ (Number _) y = throw $ TypeMismatch "numeric op " y
numCmp _ x _ = throw $ TypeMismatch "numeric op " x

eqCmd :: LispVal -> LispVal -> Eval LispVal
eqCmd (Atom x) (Atom y) = return . Bool $ x == y
eqCmd (Number x) (Number y) = return . Bool $ x == y
eqCmd (String x) (String y) = return . Bool $ x == y
eqCmd (Bool x) (Bool y) = return . Bool $ x == y
eqCmd Nil Nil = return $ Bool True
eqCmd _ _ = return $ Bool False

{-# LANGUAGE LambdaCase #-}

module Server where

{- The Server acts as a juiced-up interpreter/REPL, except programs send and
    receive messages, enabling the interpreter to provide linting, hot reload
    and more. -}

import Server.Message

import Data.Text (Text, pack)
import qualified Data.Map as Map
import Control.Concurrent
import Control.Concurrent.STM


import Data (EvalM,
             Normal,
             Normal'(NormSct, NormSig),
             CollVal(..),
             Environment,
             ProgState)

import Server.Data  
import Server.Interpret

  

startServer :: ProgState -> Environment -> IO ()  
startServer dstate denvironment  = do 
  shared <- atomically $ newTQueue 
  forkIO $ server shared
  interpreter (IState dstate denvironment (Right emptyTree)) shared




-- Server/IO Section  
server :: TQueue Message -> IO ()
server outbox = do
  atomically $ writeTQueue outbox $ UpdateModule ["lib"] (pack "(module lib (export dostuff)) (def mystring \"hello, world!\") (def dostuff (sys.put_line mystring))")
  atomically $ writeTQueue outbox $ UpdateModule [] (pack "(module main (import lib)) (def main lib.dostuff)")
  atomically $ writeTQueue outbox Compile
  atomically $ writeTQueue outbox RunMain
  atomically $ writeTQueue outbox Kill
  pure ()
  


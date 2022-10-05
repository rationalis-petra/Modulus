{-# LANGUAGE LambdaCase #-}

module Server where

{- The Server acts as a juiced-up interpreter/REPL, except programs send and
    receive messages, enabling the interpreter to provide linting, hot reload
    and more. -}


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

import Server.Message
import Server.Data  
import Server.Interpret

import Control.Monad (unless, forever, void)
import qualified Data.ByteString as Bs
import Network.Socket
import Network.Socket.ByteString (recv, sendAll)
import qualified Control.Exception as Ex


-- TODO: start server on host: localhost  
--                       port: 4008

startServer :: ProgState -> Environment -> IO ()  
startServer dstate denvironment  = do 
  byteQueue <- atomically $ newTQueue 
  messageQueue <- atomically $ newTQueue 
  forkIO $ runTCPServer Nothing "4008" (serverLoop byteQueue)
  forkIO $ messageParser byteQueue messageQueue
  interpreter (IState dstate denvironment (Right emptyTree)) messageQueue



-- start a server which listens for incoming bytestrings
-- from the "network-run" package.
runTCPServer :: Maybe HostName -> ServiceName -> (Socket -> IO a) -> IO a
runTCPServer mhost port server = withSocketsDo $ do
    addr <- resolve
    Ex.bracket (open addr) close loop
  where
    resolve = do
        let hints = defaultHints {
                addrFlags = [AI_PASSIVE]
              , addrSocketType = Stream
              }
        head <$> getAddrInfo (Just hints) mhost (Just port)
    open addr = Ex.bracketOnError (openSocket addr) close $ \sock -> do
        setSocketOption sock ReuseAddr 1
        withFdSocket sock setCloseOnExecIfNeeded
        bind sock $ addrAddress addr
        listen sock 1024
        return sock
    loop sock = forever $ Ex.bracketOnError (accept sock) (close . fst)
        $ \(conn, _peer) -> void $
            -- 'forkFinally' alone is unlikely to fail thus leaking @conn@,
            -- but 'E.bracketOnError' above will be necessary if some
            -- non-atomic setups (e.g. spawning a subprocess to handle
            -- @conn@) before proper cleanup of @conn@ is your case
            forkFinally (server conn) (const $ gracefulClose conn 5000)

serverLoop :: TQueue Bs.ByteString -> Socket -> IO ()  
serverLoop outbox socket = do 
  msg <- recv socket 1024
  unless (Bs.null msg) $ do
    atomically $ writeTQueue outbox msg
  serverLoop outbox socket

messageParser :: TQueue Bs.ByteString -> TQueue Message -> IO ()
messageParser bytes messages = do 
  _ <- atomically $ readTQueue bytes
  -- TODO use a reducer to emulate state; return messages when appropriate 
  atomically $ writeTQueue messages RunMain
  messageParser bytes messages
  
  

-- Server/IO Section  
server :: TQueue Message -> IO ()
server outbox = do
  atomically $ writeTQueue outbox $ UpdateModule ["lib"] (pack "(module lib (export dostuff)) (def mystring \"hello, world!\") (def dostuff (sys.put_line mystring))")
  atomically $ writeTQueue outbox $ UpdateModule [] (pack "(module main (import lib)) (def main lib.dostuff)")
  atomically $ writeTQueue outbox Compile
  atomically $ writeTQueue outbox RunMain
  atomically $ writeTQueue outbox Kill
  pure ()
  


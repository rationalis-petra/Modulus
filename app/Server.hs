{-# LANGUAGE LambdaCase #-}

module Server where

{- The Server acts as a juiced-up interpreter/REPL, except programs send and
    receive messages, enabling the interpreter to provide linting, hot reload
    and more. -}


import Data.Text (Text, pack, unpack)
import Data.Text.Encoding (decodeUtf8')
import qualified Data.Map as Map
import Control.Concurrent
import Control.Concurrent.STM



import Data (EvalM,
             Normal,
             Normal'(NormSct, NormSig),
             CollVal(..),
             Environment,
             ProgState)

import qualified Server.Message as Message
import Server.Message hiding (parse)
import Server.Data  
import Server.Interpret

import Bindings.Libtdl

import Control.Monad (when, unless, forever, void)
import Data.ByteString (empty, ByteString)
import qualified Data.ByteString as Bs
import Network.Socket
import Network.Socket.ByteString (recv, sendAll)
import qualified Control.Exception as Ex


-- TODO: start server on host: localhost  
--                       port: 4008

startServer :: ProgState -> Environment -> IO ()  
startServer dstate denvironment  = do 
  retCode <- dlinit 
  if not (retCode < 0) then do
    messageQueue <- atomically $ newTQueue 
    forkIO $ runTCPServer Nothing "4008" (serverLoop messageQueue)
    interpreter (IState dstate denvironment (Right emptyTree)) messageQueue
  else
    putStrLn "dlinit failed"



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
              , addrSocketType = Stream}
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


serverLoop :: TQueue Message -> Socket -> IO ()  
serverLoop outbox socket = do 
  msg <- getMessage socket 
  unless (Bs.null msg) $ do
    case decodeUtf8' msg of 
      Left err -> putStrLn ("packet decoding failed. error: " <> show err)
      Right str -> case Message.parse str of 
        Just msg -> atomically $ writeTQueue outbox msg
        Nothing -> putStrLn ("bad message: " <> unpack str)
        --Left err -> putStrLn ("packet parsing failed: " <> err)
  serverLoop outbox socket

getMessage :: Socket -> IO ByteString
getMessage socket = do
  -- just get the header (always 4 bytes)
  sizeStr <- recv socket 4
  if Bs.length sizeStr /= 4 then do
    putStrLn "header size < 4!"
    -- TODO flush/clear data?
    getMessage socket
  else accumTill (getSize sizeStr) Bs.empty

  where 
    accumTill :: Int -> Bs.ByteString -> IO ByteString
    accumTill 0 str = pure str
    accumTill n str = do
      let amt = if n < 1024 then n else 1024
      bytes <- recv socket amt
      accumTill (n - Bs.length bytes) (str <> bytes) 

    getSize :: ByteString -> Int
    getSize bs =   
      snd $ Bs.foldr (\byte (count, accum) -> (count * 256, fromEnum byte * count + accum)) (1, 0) bs

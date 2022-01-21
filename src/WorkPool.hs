
module WorkPool (runtasks) where

import Control.Concurrent
import Control.Exception
-- import Control.Concurrent.QSem
-- import Control.Concurrent.MVar
import Data.Time.Clock
import Control.Monad

overseer :: Show name => MVar () -> UTCTime -> ThreadId -> name -> IO ()
overseer ready time threadId taskName = do
  r <- tryTakeMVar ready
  case r of
    Just _ -> do
        putStrLn $ "Task " ++ show taskName ++ " finished on time."
    Nothing -> do
      cTime <- getCurrentTime
      -- putStrLn $ "Checking " ++ taskName ++ "is now: " ++ show cTime
      if cTime > time
      then do
        putStrLn $ "Task " ++ show taskName ++ " killed."
        killThread threadId
      else do
        threadDelay 100000 -- in microseconds
        overseer ready time threadId taskName

runtask :: Show name => MVar (Maybe a) -> QSem -> name -> NominalDiffTime -> IO a -> IO ()
runtask outVar poolSem taskName taskMaxTime task = do
  threadReady <- newEmptyMVar
  _ <- forkOS $
       bracket_ (waitQSem poolSem) (signalQSem poolSem >> putMVar threadReady () >> tryPutMVar outVar Nothing) $ do
         cTime <- getCurrentTime
         let endTime = addUTCTime taskMaxTime cTime
         putStrLn $ "Launching task " ++ show taskName ++ ", should end " ++ show endTime
         threadId <- myThreadId
         _ <- forkIO $ overseer threadReady endTime threadId taskName
         r <- task
         _ <- tryPutMVar outVar (Just r)
         return ()
  return ()

runtasks :: Show name => Int -> [(name,NominalDiffTime,IO a)] -> IO [(name,Maybe a)]
runtasks poolSize tasks = do
  poolSem <- newQSem poolSize
  resultVars <- forM tasks $ \(tName,tMaxTime,t) -> do
    outVar <- newEmptyMVar
    _ <- forkIO (runtask outVar poolSem tName tMaxTime t)
    return outVar
  forM (zip tasks resultVars) $ \((tName,_tMaxTime,_t),var) -> do
    x <- takeMVar var
    return (tName,x)
  -- forM_ [1..poolSize] $ \_ -> waitQSem poolSem -- wait until all tasks are finished.
  -- putStrLn $ "Complete!"



-- example = runtasks 3 [(show i,2,putStrLn ("TSK" ++ show i) >> threadDelay (1000000*i) >> putStrLn ("DON" ++ show i)) | i <- [0..10]]


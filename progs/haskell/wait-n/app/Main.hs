module Main (main) where

import Control.Exception (assert)
import Control.Concurrent.Async (runConcurrently, Concurrently(Concurrently))
import Data.Time.Clock

waitN :: Traversable t => t (Concurrently a) -> Concurrently (t a)
waitN = sequenceA

main :: IO ()
main = do
    start <- getCurrentTime
    let futs = map (Concurrently . return) [0..1000] :: [Concurrently Int]
    ns <- runConcurrently $ waitN futs
    () <- assert (sum ns == 500500) (return ())
    end <- getCurrentTime
    let elapsed = diffUTCTime end start
    putStrLn $ "done " ++ show (elapsed * 1000000) ++ "μs"

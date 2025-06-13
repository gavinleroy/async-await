module Main (main) where

import Control.Exception (assert)
import Control.Concurrent.Async (runConcurrently, Concurrently(Concurrently))
import Control.Applicative
import Data.Time.Clock

-- TODO, there's gotta be a way to write this in one line using a crazy
-- combination of type classes whose definitions I don't understand ...
-- NOTE, <|> cancels the task that didn't finish first
raceN :: [Concurrently a] -> Concurrently (Maybe a)
raceN [] = pure Nothing
raceN (x:xs) = Just <$> foldl (<|>) x xs

main :: IO ()
main = do
    start <- getCurrentTime
    let n = 42 :: Int
    let makeFut i = if i == n then (Concurrently (return i)) else empty
    let futs = [makeFut i  | i <- [0..1000]]
    res <- runConcurrently $ raceN futs
    () <- assert (res == Just n) (return ())
    end <- getCurrentTime
    let elapsed = diffUTCTime end start
    putStrLn $ "done " ++ show (elapsed * 1000000) ++ "μs"

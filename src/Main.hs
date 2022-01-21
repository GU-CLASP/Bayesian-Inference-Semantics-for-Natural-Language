import Montague
import AllProblems
import System.Environment
import WorkPool
import Text.Printf
import Data.List (sortBy)
import Data.Function (on)
import Data.Maybe (listToMaybe)
import Control.Monad (forM, when)
import PreciseProb

getTagValue :: Read a => Integer -> String -> Maybe a
getTagValue n tag = listToMaybe [read x | [s,x] <- tags n, s == tag]

hasTag :: Integer -> [Char] -> Bool
hasTag n tag = [tag] `elem` tags n


runN :: Integer -> IO Double
runN n = do
  let s = unlines $ input n
  putStrLn s
  let iterations = (maybe 10000 id (getTagValue n "iterations"))
      runs = (maybe 1 id (getTagValue n "runs"))
  rs <- forM [1..runs] $ \i -> do
    ri <- run' iterations (problem n)
    putStrLn $ "Run " ++ show i ++ " True: " ++ show ri
    return (probToDouble ri)
  let r = sum rs / fromInteger runs
  let r' = ("True:" ++ show r)
  writeFile ("result" ++ printf "%02d" n) (unlines [s,r'])
  when (runs > 1) $ do
    putStrLn $ "Average: " ++ show r
  return r

summaryLine :: (Integer,Maybe Double) -> String
summaryLine (name,r) = printf "problem %02d  %7s %s" name s (show r)
  where s = if hasTag name "noparse"
            then "NOPARSE"
            else case r of
                   Nothing -> "TIMEOUT"
                   Just x | x >= 0.5 -> "PASSED "
                   _ -> "FAILED "

main :: IO ()
main = do
  pb <- concatMap words <$> getArgs
  print pb
  case pb of
    ["par",parallelTasks,maxTime] -> do
      results <- runtasks (read parallelTasks::Int) [(n, fromInteger (read maxTime :: Integer),runN n) | n <- [1..numberOfProblems]]
      putStrLn $ unlines $ map summaryLine $ sortBy (compare `on` fst) $ results
    ["all"] -> mapM_ runN [1..numberOfProblems]
    [pbNumber] -> runN (read pbNumber) >> return ()
    _ -> error "Incorrect arguments"



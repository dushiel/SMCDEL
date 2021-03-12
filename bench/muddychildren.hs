module Main where

import Criterion.Main
import Data.Function
import Data.List

import SMCDEL.Language
import SMCDEL.Examples.MuddyChildren
import System.IO.Unsafe
import SMCDEL.Internal.Help (apply)
import qualified SMCDEL.Explicit.DEMO_S5 as DEMO_S5
import qualified SMCDEL.Explicit.S5
import qualified SMCDEL.Symbolic.S5
import qualified SMCDEL.Symbolic.S5_CUDD
import qualified SMCDEL.Translations.S5
import qualified SMCDEL.Translations.K
import qualified SMCDEL.Other.MCTRIANGLE
import qualified SMCDEL.Symbolic.K

checkForm :: Int -> Int -> Form
checkForm n 0 = nobodyknows n
checkForm n k = PubAnnounce (nobodyknows n) (checkForm n (k-1))

findNumberWith :: (Int -> Int -> a, a -> Form -> Bool) -> Int -> Int -> Int
findNumberWith (start,evalfunction) n m = k where
  k | loop 0 == (m-1) = m-1
    | otherwise       = error $ "wrong Muddy Children result: " ++ show (loop 0)
  loop count = if evalfunction (start n m) (PubAnnounce (father n) (checkForm n count))
    then loop (count+1)
    else count

mudPs :: Int -> [Prp]
mudPs n = [P 1 .. P n]

findNumberCacBDD :: Int -> Int -> Int
findNumberCacBDD = findNumberWith (cacMudScnInit,SMCDEL.Symbolic.S5.evalViaBdd) where
  cacMudScnInit n m = ( SMCDEL.Symbolic.S5.KnS (mudPs n) (SMCDEL.Symbolic.S5.boolBddOf Top) [ (show i,delete (P i) (mudPs n)) | i <- [1..n] ], mudPs m )

findNumberCUDDZ :: Int -> Int -> Int
findNumberCUDDZ n m = unsafePerformIO $ do
  SMCDEL.Symbolic.S5_CUDD.initZddVars [ 1 .. n ]
  let cuddMudScnInit x y = ( SMCDEL.Symbolic.S5_CUDD.KnSZ (mudPs x) (SMCDEL.Symbolic.S5_CUDD.boolZddOf (mudPs x) Top) [ (show i,delete (P i) (mudPs x)) | i <- [1..x] ], mudPs y )
  let result = findNumberWith (cuddMudScnInit, SMCDEL.Symbolic.S5_CUDD.evalViaDd) n m 
  return result

findNumberCUDDZs0 :: Int -> Int -> Int
findNumberCUDDZs0 n m = unsafePerformIO $ do
  SMCDEL.Symbolic.S5_CUDD.initZddVars [ 1 .. n ]
  let cuddMudScnInit x y = ( SMCDEL.Symbolic.S5_CUDD.KnSZs0 (mudPs x) (SMCDEL.Symbolic.S5_CUDD.boolZdds0Of (mudPs x) Top) [ (show i,delete (P i) (mudPs x)) | i <- [1..x] ], mudPs y )
  let result = findNumberWith (cuddMudScnInit, SMCDEL.Symbolic.S5_CUDD.evalViaDd) n m 
  return result

findNumberCUDDZf0 :: Int -> Int -> Int
findNumberCUDDZf0 n m = unsafePerformIO $ do
  SMCDEL.Symbolic.S5_CUDD.initZddVars [ 1 .. n ]
  let cuddMudScnInit x y = ( SMCDEL.Symbolic.S5_CUDD.KnSZf0 (mudPs x) (SMCDEL.Symbolic.S5_CUDD.boolZddf0Of (mudPs x) Top) [ (show i,delete (P i) (mudPs x)) | i <- [1..x] ], mudPs y )
  let result = findNumberWith (cuddMudScnInit, SMCDEL.Symbolic.S5_CUDD.evalViaDd) n m 
  return result

findNumberCUDDZf0s0 :: Int -> Int -> Int
findNumberCUDDZf0s0 n m = unsafePerformIO $ do
  SMCDEL.Symbolic.S5_CUDD.initZddVars [ 1 .. n ]
  let cuddMudScnInit x y = ( SMCDEL.Symbolic.S5_CUDD.KnSZf0s0 (mudPs x) (SMCDEL.Symbolic.S5_CUDD.boolZddf0s0Of (mudPs x) Top) [ (show i,delete (P i) (mudPs x)) | i <- [1..x] ], mudPs y )
  let result = findNumberWith (cuddMudScnInit, SMCDEL.Symbolic.S5_CUDD.evalViaDd) n m 
  return result

findNumberCUDD :: Int -> Int -> Int
findNumberCUDD = findNumberWith (cuddMudScnInit,SMCDEL.Symbolic.S5_CUDD.evalViaBdd) where
  cuddMudScnInit n m = ( SMCDEL.Symbolic.S5_CUDD.KnS (mudPs n) (SMCDEL.Symbolic.S5_CUDD.boolBddOf Top) [ (show i,delete (P i) (mudPs n)) | i <- [1..n] ], mudPs m )

findNumberTrans :: Int -> Int -> Int
findNumberTrans = findNumberWith (start,SMCDEL.Symbolic.S5.evalViaBdd) where
  start n m = SMCDEL.Translations.S5.kripkeToKns $ mudKrpInit n m

mudKrpInit :: Int -> Int -> SMCDEL.Explicit.S5.PointedModelS5
mudKrpInit n m = (SMCDEL.Explicit.S5.KrMS5 ws rel val, cur) where
  ws    = [0..(2^n-1)]
  rel   = [ (show i, erelFor i) | i <- [1..n] ] where
    erelFor i = sort $ map sort $
      groupBy ((==) `on` setForAt i) $
      sortOn (setForAt i) ws
    setForAt i s = delete (P i) $ setAt s
    setAt s = map fst $ filter snd (apply val s)
  val         = zip ws table
  ((cur,_):_) = filter (\(_,ass)-> sort (map fst $ filter snd ass) == [P 1..P m]) val
  table = foldl buildTable [[]] [P k | k<- [1..n]]
  buildTable partrows p = [ (p,v):pr | v <-[True,False], pr<-partrows ]

findNumberK :: Int -> Int -> Int
findNumberK = findNumberWith (mudBelScnInit, SMCDEL.Symbolic.K.evalViaBdd)

findNumberTransK :: Int -> Int -> Int
findNumberTransK = findNumberWith (start,SMCDEL.Symbolic.K.evalViaBdd) where
  start n m = SMCDEL.Translations.K.kripkeToBls $ mudGenKrpInit n m

mudDemoKrpInit :: Int -> Int -> DEMO_S5.EpistM [Bool]
mudDemoKrpInit n m = DEMO_S5.Mo states agents [] rels points where
  states = DEMO_S5.bTables n
  agents = map DEMO_S5.Ag [1..n]
  rels = [(DEMO_S5.Ag i, [[tab1++[True]++tab2,tab1++[False]++tab2] |
                   tab1 <- DEMO_S5.bTables (i-1),
                   tab2 <- DEMO_S5.bTables (n-i) ]) | i <- [1..n] ]
  points = [replicate (n-m) False ++ replicate m True]

findNumberDemoS5 :: Int -> Int -> Int
findNumberDemoS5 n m = findNumberDemoLoop n m 0 start where
  start = DEMO_S5.updPa (mudDemoKrpInit n m) (DEMO_S5.fatherN n)

findNumberDemoLoop :: Int -> Int -> Int -> DEMO_S5.EpistM [Bool] -> Int
findNumberDemoLoop n m count curMod =
  if DEMO_S5.isTrue curMod (DEMO_S5.dont n)
    then findNumberDemoLoop n m (count+1) (DEMO_S5.updPa curMod (DEMO_S5.dont n))
    else count

findNumberTriangle :: Int -> Int -> Int
findNumberTriangle n m = findNumberTriangleLoop 0 start where
  start = SMCDEL.Other.MCTRIANGLE.mcUpdate (SMCDEL.Other.MCTRIANGLE.mcModel (n-m,m)) (SMCDEL.Other.MCTRIANGLE.Qf SMCDEL.Other.MCTRIANGLE.some)

findNumberTriangleLoop :: Int -> SMCDEL.Other.MCTRIANGLE.McModel -> Int
findNumberTriangleLoop count curMod =
  if SMCDEL.Other.MCTRIANGLE.eval curMod SMCDEL.Other.MCTRIANGLE.nobodyknows
    then findNumberTriangleLoop (count+1) (SMCDEL.Other.MCTRIANGLE.mcUpdate curMod SMCDEL.Other.MCTRIANGLE.nobodyknows)
    else count

main :: IO ()
main = 
    defaultMain (map mybench
  [ ("CUDDZ"     , findNumberCUDDZ     , [3..40] )
  , ("CUDDZs0"   , findNumberCUDDZs0   , [3..40] )
  , ("CUDDZf0"   , findNumberCUDDZf0   , [3..40] )
  , ("CUDDZf0s0" , findNumberCUDDZf0s0 , [3..40] )
  , ("K"         , findNumberK         , [3..12] )
  , ("Triangle"  , findNumberTriangle  , [7..40] )
  , ("CacBDD"    , findNumberCacBDD    , [3..40] )
  , ("CUDD"      , findNumberCUDD      , [3..40] )
  , ("DEMOS5"    , findNumberDemoS5    , [3..12] )
  , ("Trans"     , findNumberTrans     , [3..12] )
  , ("TransK"    , findNumberTransK    , [3..11] ) ])
  where
    mybench (name,f,range) = bgroup name $ map (run f) range
    run f k = bench (show k) $ whnf (\n -> f n n) k

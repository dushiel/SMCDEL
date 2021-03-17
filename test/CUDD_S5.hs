module Main (main) where

import Data.Dynamic (toDyn)
import Data.Map.Strict (fromList)
import Data.List (sort)
import Test.Hspec
import Test.Hspec.QuickCheck

import SMCDEL.Internal.Help (alleq)
import SMCDEL.Language
import SMCDEL.Symbolic.S5_CUDD as Cudd

import Debug.Trace (trace)

main :: IO ()
main = do 
  initZddVars [1..5]
  hspec $ do
    describe "hardcoded myScn" $ do
      prop "evalVia on different DD types" $ alleq . comparisonDdTest --How are the forms given on here?
      --prop "conversion to different DD types" $ alleq . conversionDdTest




myKnS :: Cudd.KnowStruct
myKnS = Cudd.KnS myDefaultProps (boolBddOf Top) myDefaultObservables `debug` "init bdd"

myKnSZ :: Cudd.KnowStruct
myKnSZ = Cudd.KnSZ myDefaultProps (boolZddOf myDefaultProps Top) myDefaultObservables

myKnSZs0 :: Cudd.KnowStruct
myKnSZs0 = Cudd.KnSZs0 myDefaultProps (boolZdds0Of myDefaultProps Top) myDefaultObservables

myKnSZf0 :: Cudd.KnowStruct
myKnSZf0 = Cudd.KnSZf0 myDefaultProps (boolZddf0Of myDefaultProps Top) myDefaultObservables

myKnSZf0s0 :: Cudd.KnowStruct
myKnSZf0s0 = Cudd.KnSZf0 myDefaultProps (boolZddf0s0Of myDefaultProps Top) myDefaultObservables

myDefaultState :: [Prp]
myDefaultState = [P 1 .. P 5] 

myDefaultProps :: [Prp]
myDefaultProps = [P 1 .. P 5]

myDefaultObservables :: [(Agent,[Prp])]
myDefaultObservables = [("1", [P 1 .. P 5]), ("2", [P 1, P 2]), ("3", [])]

comparisonDdTest :: SimplifiedForm -> [Bool]
comparisonDdTest (SF f) = 
  [ Cudd.evalViaBdd (myKnS, myDefaultState) f 
    , Cudd.evalViaDd (myKnSZ, myDefaultState) f 
    --, Cudd.evalViaDd (myKnSZs0, myDefaultState) f
    --, Cudd.evalViaDd (myKnSZf0, myDefaultState) f
    --, Cudd.evalViaDd (myKnSZf0s0, myDefaultState) f
  ]

conversionDdTest :: SimplifiedForm -> [Bool]
conversionDdTest (SF f) = 
  [ Cudd.evalViaDd (myKnS, myDefaultState) f
    , Cudd.evalViaDd (Cudd.convertToZdd myKnS, myDefaultState) f
    , Cudd.evalViaDd (Cudd.convertToZdds0 myKnS, myDefaultState) f
    , Cudd.evalViaDd (Cudd.convertToZddf0 myKnS, myDefaultState) f
    , Cudd.evalViaDd (Cudd.convertToZddf0s0 myKnS, myDefaultState) f
  ]

--debug :: c -> String -> c
--debug = flip trace
--are the functions below also useful for me?
{-diffTest :: PointedModel -> PointedModel -> Bool
diffTest pmA pmB =
  case diffPointed pmA pmB of
    Left  b -> checkBisimPointed b pmA pmB
    Right f -> isTrue pmA f && not (isTrue pmB f)


myMod :: ExpK.PointedModel
myMod = (ExpK.KrM $ fromList wlist, 0) where
  wlist = [ (w, (fromList val, fromList $ relFor val)) | (val,w) <- wvals ]
  vals  = map sort (foldl buildTable [[]] [P 0 .. P 4])
  wvals = zip vals [0..]
  buildTable partrows p = [ (p,v):pr | v <-[True,False], pr <- partrows ]
  relFor val = [ (show i, map snd $ seesFrom i val) | i <- [0..5::Int] ]
  seesFrom i val = filter (\(val',_) -> samefor i val val') wvals
  samefor 0 ps qs = ps == qs  -- knows everything
  samefor 1 _  _  = False     -- insane
  samefor _ _  _  = True

myScn :: SymK.BelScene
myScn =
  let allprops = [P 0 .. P 4]
  in (SymK.BlS allprops
                  (boolBddOf Top)
                  (fromList $ ("0", SymK.allsamebdd allprops)  -- knows everything
                            : ("1", SymK.emptyRelBdd)          -- insane
                            : [(show i, SymK.totalRelBdd) | i<-[2..5::Int]])
     , allprops)-}
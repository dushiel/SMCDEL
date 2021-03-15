module Main (main) where

import Data.Dynamic (toDyn)
import Data.Map.Strict (fromList)
import Data.List (sort)
import Test.Hspec
import Test.Hspec.QuickCheck

import SMCDEL.Internal.Help (alleq)
import SMCDEL.Language
import SMCDEL.Symbolic.S5_CUDD as Cudd

main :: IO ()
main = hspec $ do
  describe "hardcoded myScn" $ do
    prop "evalVia on different DD types" $ alleq . comparisonDdTest --How are the forms given on here?
    prop "conversion to different DD types" $ alleq . conversionDdTest

  describe "random Kripke models" $ do
    prop "Ck i -> K i" $ \(Ag i) krm f -> ExpK.eval (krm,0) (Ck [i] f `Impl` Ck [i] f) --same here, how is f and i determined? does it have to do with the arrow? how does the single backslash work?
    prop "semanticEquivExpToSym" $ \krm f -> alleq $ semanticEquivExpToSym (krm,0) f
    prop "diff" $ \krmA krmB -> diffTest (krmA,0) (krmB,0)

--Test cases!:

--Law: Forall 1 ((2 & ~ 1) -> (~3))
--Valid: Exists 1 ((~ 1 -> (~3)) & (2 -> (~3 | 1)))


--Law: Top
-- [ ! (1) ] alice knows that (1)


--Law: 1   
-- [ ! ((alice knows whether 1) & (bob knows whether 1) & (carol knows whether 1)) ] 
-- (alice, bob, carol) comknows that (1 & 2 & 3)

--Law: Top
-- alice knows that (1 -> ~2) [?! (1 & 2 & 3)] alice knows that ~(1 & 2 & 3 )

--Law: Top
-- alice knows that (1 -> ~2) [ (alice, bob) ?! (1 & 2 & 3)] alice knows that ~(1 & 2 & 3 )


myKnS :: Cudd.KnowStruct
myKnS = 
  (Cudd.KnS [P 0 .. P 4], boolBddOf Top, obs) --how to create instance of obs

myKnSZ :: Cudd.KnowStruct
myKnSZ = 
  (Cudd.KnSZ [P 0 .. P 4], boolZddOf Top, obs)

myKnSZs0 :: Cudd.KnowStruct
myKnSZs0 = 
  (Cudd.KnSZs0 [P 0 .. P 4], boolZdds0Of Top, obs)

myKnSZf0 :: Cudd.KnowStruct
myKnSZf0 = 
  (Cudd.KnSZf0 [P 0 .. P 4], boolZddf0Of Top, obs)

myKnSZf0s0 :: Cudd.KnowStruct
myKnSZf0s0 = 
  (Cudd.KnSZf0 [P 0 .. P 4], boolZddf0s0Of Top, obs)

myState :: [Prp]
myState = [P 0 .. P 4] --do i want to variate this?

comparisonDdTest :: SimplifiedForm -> [Bool]
comparisonToBddTest (SF f) = 
  [ Cudd.evalViaDd myCuddScene f
    , Cudd.evalViaDd myCuddSceneZ f
    , Cudd.evalViaDd myCuddSceneZs0 f
    , Cudd.evalViaDd myCuddSceneZf0 f
    , Cudd.evalViaDd myCuddSceneZf0s0 f
  ]

conversionDdTest :: SimplifiedForm -> [Bool]
comparisonToBddTest (SF f) = 
  [ Cudd.evalViaDd (myKnS, myState) f
    , Cudd.evalViaDd (Cudd.convertToZdd myKnS, myState) f
    , Cudd.evalViaDd (Cudd.convertToZdds0 myKnS, myState) f
    , Cudd.evalViaDd (Cudd.convertToZddf0 myKnS, myState) f
    , Cudd.evalViaDd (Cudd.convertToZddf0s0 myKnS, myState) f
  ]


--are the functions below also useful for me?
diffTest :: PointedModel -> PointedModel -> Bool
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
     , allprops)
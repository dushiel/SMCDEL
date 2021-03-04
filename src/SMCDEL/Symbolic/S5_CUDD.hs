{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

module SMCDEL.Symbolic.S5_CUDD where

import SMCDEL.Internal.MyHaskCUDD
import Data.List ((\\))
import SMCDEL.Internal.Help (apply)
import SMCDEL.Language
import System.IO.Unsafe ( unsafePerformIO )
import Data.List ((\\),delete,dropWhile,dropWhileEnd,intercalate,intersect,nub,sort)
--import Data.Tagged
import SMCDEL.Internal.TexDisplay ( TexAble(tex) )
import System.Process (runInteractiveCommand)
import System.IO (hPutStr, hGetContents, hClose)
import Data.Char (isSpace)
--------------------------
import Data.GraphViz
    ( parseDotGraphLiberally,
      PrintDot(toDot),
      DotEdge(toNode, fromNode),
      DotNode(nodeID) )  
import qualified Data.Text.Lazy as B
import qualified Data.GraphViz.Types.Generalised as DotGen
import Data.GraphViz.Printing (renderDot)

---------------------------
import Control.DeepSeq (rnf)
import Data.Typeable()

-- Data types

data KnowStruct = 
  KnS [Prp] !(Dd B) [(Agent,[Prp])] 
  | KnSZ [Prp] !(Dd Z) [(Agent,[Prp])] 
  | KnSZs0 [Prp] !(Dd Z) [(Agent,[Prp])] 
  | KnSZf0 [Prp] !(Dd Z) [(Agent,[Prp])] 
  | KnSZf0s0 [Prp] !(Dd Z) [(Agent,[Prp])] 
  deriving (Eq,Show)
type KnState = [Prp] 
type KnowScene = (KnowStruct,KnState)

instance HasVocab KnowStruct where
  vocabOf (KnS props _ _) = props
  vocabOf (KnSZ props _ _) = props
  vocabOf (KnSZs0 props _ _) = props
  vocabOf (KnSZf0 props _ _) = props
  vocabOf (KnSZf0s0 props _ _) = props

instance Pointed KnowStruct KnState



--------------querying

validViaDd :: KnowStruct -> Form -> Bool
validViaDd kns@(KnS _ lawbdd _) f = top == lawbdd `imp` bddOf kns f
validViaDd kns@(KnSZ _ lawzdd _) f = topZ == lawzdd `imp` zddOf kns f
validViaDd kns@(KnSZs0 _ lawzdd _) f = topZ == lawzdd `imp` zdds0Of kns f
validViaDd kns@(KnSZf0 _ lawzdd _) f = topZ == zddf0Of kns f `imp` lawzdd
validViaDd kns@(KnSZf0s0 _ lawzdd _) f = topZ == zddf0s0Of kns f `imp` lawzdd 

evalViaDd :: KnowScene -> Form -> Bool
evalViaDd (kns@(KnS allprops _ _),s) f = bool where
  bool | b==top = True
       | b==bot = False
       | otherwise = error ("evalViaDd failed: BDD leftover:\n" ++ show b)
  b    = restrictSet (bddOf kns f) list
  list = [ (n, P n `elem` s) | (P n) <- allprops ]
evalViaDd (kns@(KnSZ allprops _ _),s) f = bool where
  bool | z==topZ = True
       | z==botZ = False
       | otherwise = error ("evalViaDd failed: ZDD leftover:\n" ++ show z)
  z    = restrictSet (zddOf kns f) list
  list = [ (n, P n `elem` s) | (P n) <- allprops ]
evalViaDd (kns@(KnSZs0 allprops _ _),s) f = bool where -- Not done yet!!
  bool | z==topZ = True
       | z==botZ = False
       | otherwise = error ("evalViaDd failed: ZDDs0 leftover:\n" ++ show z)
  z    = restrictSet (zdds0Of kns f) list
  list = [ (n, P n `elem` s) | (P n) <- allprops ]
evalViaDd (kns@(KnSZf0 allprops _ _),s) f = bool where
  bool | z==botZ = True
       | z==topZ = False
       | otherwise = error ("evalViaDd failed: ZDDf0 leftover:\n" ++ show z)
  z    = restrictSet (zddOf kns f) list
  list = [ (n, P n `elem` s) | (P n) <- allprops ]
evalViaDd (kns@(KnSZf0s0 allprops _ _),s) f = bool where -- Not done yet!!
  bool | z==botZ = True
       | z==topZ = False
       | otherwise = error ("evalViaDd failed: ZDDf0s0 leftover:\n" ++ show z)
  z    = restrictSet (zdds0Of kns f) list
  list = [ (n, P n `elem` s) | (P n) <- allprops ]


-- Transformations acting on knowledge structs (PAL)

pubAnnounce :: KnowStruct -> Form -> KnowStruct
pubAnnounce kns@(KnS props lawbdd obs) psi = KnS props newlawbdd obs where
  newlawbdd = con lawbdd (bddOf kns psi)
pubAnnounce kns@(KnSZ props lawzdd obs) psi = KnSZ props newlawzdd obs where
  newlawzdd = con lawzdd (zddOf kns psi)
pubAnnounce kns@(KnSZs0 props lawzdd obs) psi = KnSZs0 props newlawzdd obs where
  newlawzdd = con lawzdd (zdds0Of kns psi)
pubAnnounce kns@(KnSZf0 props lawzdd obs) psi = KnSZf0 props newlawzdd obs where
  newlawzdd = con lawzdd (zddf0Of kns psi)
pubAnnounce kns@(KnSZf0s0 props lawzdd obs) psi = KnSZf0s0 props newlawzdd obs where
  newlawzdd = con lawzdd (zddf0s0Of kns psi)

announce :: KnowStruct -> [Agent] -> Form -> KnowStruct
announce kns@(KnS props lawbdd obs) ags psi = KnS newprops newlawbdd newobs where
  proppsi@(P k) = freshp props
  newprops  = proppsi:props
  newlawbdd = con lawbdd (equ (var k) (bddOf kns psi))
  newobs    = [(i, apply obs i ++ [proppsi | i `elem` ags]) | i <- map fst obs]
announce kns@(KnSZ props lawzdd obs) ags psi = KnSZ newprops newlawzdd newobs where
  proppsi@(P k) = freshp props
  newprops  = proppsi:props
  newlawzdd = con lawzdd (equ (varZ k) (zddOf kns psi))
  newobs    = [(i, apply obs i ++ [proppsi | i `elem` ags]) | i <- map fst obs]
{-announce kns@(KnSZs0 props lawzdd obs) ags psi = KnSZs0 newprops newlawzdd newobs where
  proppsi@(P k) = freshp props
  newprops  = proppsi:props
  newlawzdd = con lawzdd (equ (varZ k) (zdds0Of kns psi))
  newobs    = [(i, apply obs i ++ [proppsi | i `elem` ags]) | i <- map fst obs]-}

announce _ _ _ = error "announce not implemented yet for other zdd types"




-- Tranforming Logic formulas to BDD and all ZDD forms below!

-- BDD Construction

boolBddOf :: Form -> Dd B 
boolBddOf Top           = top
boolBddOf Bot           = bot
boolBddOf (PrpF (P n))  = var n
boolBddOf (Neg form)    = neg$ boolBddOf form
boolBddOf (Conj forms)  = conSet $ map boolBddOf forms
boolBddOf (Disj forms)  = disSet  $ map boolBddOf forms
boolBddOf (Impl f g)    = imp (boolBddOf f) (boolBddOf g)
boolBddOf (Equi f g)    = equ (boolBddOf f) (boolBddOf g)
boolBddOf (Forall ps f) = boolBddOf (foldl singleForall f ps) where
  singleForall g p = Conj [ substit p Top g, substit p Bot g ]
boolBddOf (Exists ps f) = boolBddOf (foldl singleExists f ps) where
  singleExists g p = Disj [ substit p Top g, substit p Bot g ]
boolBddOf _             = error "boolBddOf failed: Not a boolean formula."

bddOf :: KnowStruct -> Form -> Dd B 
bddOf _   Top           = top
bddOf _   Bot           = bot
bddOf _   (PrpF (P n))  = var n
bddOf kns (Neg form)    = neg $ bddOf kns form
bddOf kns (Conj forms)  = conSet $ map (bddOf kns) forms
bddOf kns (Disj forms)  = disSet $ map (bddOf kns) forms
bddOf kns (Xor  forms)  = xorSet $ map (bddOf kns) forms
bddOf kns (Impl f g)    = imp (bddOf kns f) (bddOf kns g)
bddOf kns (Equi f g)    = equ (bddOf kns f) (bddOf kns g)
bddOf kns (Forall ps f) = forallSet (map fromEnum ps) (bddOf kns f)
bddOf kns (Exists ps f) = existsSet (map fromEnum ps) (bddOf kns f)
bddOf kns@(KnS allprops lawbdd obs) (K i form) =
  forallSet otherps (imp lawbdd (bddOf kns form)) where
    otherps = map (\(P n) -> n) $ allprops \\ apply obs i --what does this do?
bddOf kns@(KnS allprops lawbdd obs) (Kw i form) =
  disSet [ forallSet otherps (imp lawbdd (bddOf kns f)) | f <- [form, Neg form] ] where
    otherps = map (\(P n) -> n) $ allprops \\ apply obs i
bddOf kns@(KnS allprops lawbdd obs) (Ck ags form) = gfp lambda where
  lambda z = conSet $ bddOf kns form : [ forallSet (otherps i) (imp lawbdd z) | i <- ags ]
  otherps i = map (\(P n) -> n) $ allprops \\ apply obs i
bddOf kns (Ckw ags form) = dis (bddOf kns (Ck ags form)) (bddOf kns (Ck ags (Neg form)))
bddOf kns@(KnS props _ _) (Announce ags form1 form2) =
  imp (bddOf kns form1) (restrict bdd2 (k,True)) where
    bdd2  = bddOf (announce kns ags form1) form2
    (P k) = freshp props
bddOf kns@(KnS props _ _) (AnnounceW ags form1 form2) =
  ifthenelse (bddOf kns form1) bdd2a bdd2b where
    bdd2a = restrict (bddOf (announce kns ags form1) form2) (k,True)
    bdd2b = restrict (bddOf (announce kns ags form1) form2) (k,False)
    (P k) = freshp props
bddOf kns (PubAnnounce form1 form2) = imp (bddOf kns form1) newform2 where
    newform2 = bddOf (pubAnnounce kns form1) form2
bddOf kns (PubAnnounceW form1 form2) =
  ifthenelse (bddOf kns form1) newform2a newform2b where
    newform2a = bddOf (pubAnnounce kns form1) form2
    newform2b = bddOf (pubAnnounce kns (Neg form1)) form2
bddOf _ (Dia _ _) = error "Dynamic operators are not implemented for CUDD."
bddOf _ _ = error "bddOf with wrong kns type"

evalViaBdd :: KnowScene -> Form -> Bool 
evalViaBdd (kns@(KnS allprops _ _),s) f = bool where
  bool | b==top = True
       | b==bot = False
       | otherwise = error ("evalViaBdd failed: BDD leftover:\n" ++ show b)
  b    = restrictSet (bddOf kns f) list
  list = [ (n, P n `elem` s) | (P n) <- allprops ]
evalViaBdd (_,_) _ = error "evalViaBdd with a wrong kns type"

instance Semantics KnowScene where
  isTrue = evalViaBdd

validViaBdd :: KnowStruct -> Form -> Bool
validViaBdd kns@(KnS _ lawbdd _) f = top == lawbdd `imp` bddOf kns f
validViaBdd _ _ = error "validViaBdd with wrong kns type"




-------------- building


boolZddOf :: Form -> Dd Z
boolZddOf Top           = topZ
boolZddOf Bot           = botZ
boolZddOf (PrpF (P n))  = varZ n
boolZddOf (Neg form)    = neg (boolZddOf form)
boolZddOf (Conj forms)  = conSet $ map boolZddOf forms
boolZddOf (Disj forms)  = disSet $ map boolZddOf forms
boolZddOf (Impl f g)    = imp (boolZddOf f) (boolZddOf g)
boolZddOf (Equi f g)    = equ (boolZddOf f) (boolZddOf g)
boolZddOf (Forall ps f) = forallSet (map fromEnum ps) (boolZddOf f)
boolZddOf (Exists ps f) = existsSet (map fromEnum ps) (boolZddOf f)
boolZddOf _             = error "boolZddOf failed: Not a boolean formula."

zddOf :: KnowStruct -> Form -> Dd Z
zddOf _   Top           = topZ
zddOf _   Bot           = botZ
zddOf _   (PrpF (P n))  = varZ n
zddOf kns (Neg form) = neg (zddOf kns form)

zddOf kns (Conj forms)  = conSet $ map (zddOf kns) forms
zddOf kns (Disj forms)  = disSet $ map (zddOf kns) forms
zddOf kns (Xor  forms)  = xorSet $ map (zddOf kns) forms

zddOf kns (Impl f g)    = imp (zddOf kns f) (zddOf kns g)
zddOf kns (Equi f g)    = equ (zddOf kns f) (zddOf kns g)

zddOf kns (Forall ps f) = forallSet (map fromEnum ps) (zddOf kns f)
zddOf kns (Exists ps f) = existsSet (map fromEnum ps) (zddOf kns f)

zddOf kns@(KnSZ allprops lawzdd obs) (K i form) =
  forallSet otherps (imp lawzdd (zddOf kns form)) where
    otherps = map (\(P n) -> n) $ allprops \\ apply obs i

zddOf kns@(KnSZ allprops lawzdd obs) (Kw i form) =
  disSet [ forallSet otherps (imp lawzdd (zddOf kns f)) | f <- [form, Neg form] ] where
    otherps = map (\(P n) -> n) $ allprops \\ apply obs i

zddOf kns@(KnSZ allprops lawzdd obs) (Ck ags form) = gfpZ lambda where
  lambda z = conSet $ zddOf kns form : [ forallSet (otherps i) (imp lawzdd z) | i <- ags ]
  otherps i = map (\(P n) -> n) $ allprops \\ apply obs i

zddOf kns (Ckw ags form) = dis (zddOf kns (Ck ags form)) (zddOf kns (Ck ags (Neg form)))

zddOf kns@(KnSZ props _ _) (Announce ags form1 form2) =
  imp (zddOf kns form1) (restrict zdd2 (k,True)) where
    zdd2  = zddOf (announce kns ags form1) form2
    (P k) = freshp props

zddOf kns@(KnSZ props _ _) (AnnounceW ags form1 form2) =
  ifthenelse (zddOf kns form1) zdd2a zdd2b where
    zdd2a = restrict (zddOf (announce kns ags form1) form2) (k,True)
    zdd2b = restrict (zddOf (announce kns ags form1) form2) (k,False)
    (P k) = freshp props

zddOf kns (PubAnnounce form1 form2) = imp (zddOf kns form1) newform2 where
    newform2 = zddOf (pubAnnounce kns form1) form2

zddOf kns (PubAnnounceW form1 form2) =
  ifthenelse (zddOf kns form1) newform2a newform2b where
    newform2a = zddOf (pubAnnounce kns form1) form2
    newform2b = zddOf (pubAnnounce kns (Neg form1)) form2

zddOf _ (Dia _ _) = error "Dynamic operators are not implemented for CUDD."
zddOf _ _ = error "zddOf with a wrong kns type"

--ZDD in f1s0 form

boolZdds0Of :: Form -> Dd Z
boolZdds0Of Top           = topZ
boolZdds0Of Bot           = botZ
boolZdds0Of (PrpF (P n))  = neg (varZ n)
boolZdds0Of (Neg (PrpF (P n)))    = varZ n
boolZdds0Of (Neg form)    = neg (boolZdds0Of form)
boolZdds0Of (Conj forms)  = conSet $ map boolZdds0Of forms
boolZdds0Of (Disj forms)  = disSet $ map boolZdds0Of forms
boolZdds0Of (Impl f g)    = imp (boolZdds0Of f) (boolZdds0Of g)
boolZdds0Of (Equi f g)    = equ (boolZdds0Of f) (boolZdds0Of g)
boolZdds0Of (Forall ps f) = forallSet (map fromEnum ps) (boolZdds0Of f)
boolZdds0Of (Exists ps f) = existsSet (map fromEnum ps) (boolZdds0Of f)
boolZdds0Of _             = error "boolZdds0Of failed: Not a boolean formula."

zdds0Of :: KnowStruct -> Form -> Dd Z
zdds0Of _   Top           = topZ
zdds0Of _   Bot           = botZ
zdds0Of _   (PrpF (P n))  = neg (varZ n) -- s0 swaps these
zdds0Of _ (Neg (PrpF (P n))) = varZ n -- s0 swaps these
zdds0Of kns (Neg form) = neg (zdds0Of kns form)

zdds0Of kns (Conj forms)  = conSet $ map (zdds0Of kns) forms
zdds0Of kns (Disj forms)  = disSet $ map (zdds0Of kns) forms
zdds0Of kns (Xor  forms)  = xorSet $ map (zdds0Of kns) forms

zdds0Of kns (Impl f g)    = imp (zdds0Of kns f) (zdds0Of kns g)
zdds0Of kns (Equi f g)    = equ (zdds0Of kns f) (zdds0Of kns g)

zdds0Of kns (Forall ps f) = forallSet (map fromEnum ps) (zdds0Of kns f)
zdds0Of kns (Exists ps f) = existsSet (map fromEnum ps) (zdds0Of kns f)

zdds0Of kns@(KnSZs0 allprops lawzdd obs) (K i form) =
  forallSet otherps (imp lawzdd (zdds0Of kns form)) where
    otherps = map (\(P n) -> n) $ allprops \\ apply obs i

zdds0Of kns@(KnSZs0 allprops lawzdd obs) (Kw i form) =
  disSet [ forallSet otherps (imp lawzdd (zdds0Of kns f)) | f <- [form, Neg form] ] where
    otherps = map (\(P n) -> n) $ allprops \\ apply obs i

zdds0Of kns@(KnSZs0 allprops lawzdd obs) (Ck ags form) = gfpZ lambda where
  lambda z = conSet $ zdds0Of kns form : [ forallSet (otherps i) (imp lawzdd z) | i <- ags ]
  otherps i = map (\(P n) -> n) $ allprops \\ apply obs i

zdds0Of kns (Ckw ags form) = dis (zdds0Of kns (Ck ags form)) (zdds0Of kns (Ck ags (Neg form)))

zdds0Of kns@(KnSZs0 props _ _) (Announce ags form1 form2) =
  imp (zdds0Of kns form1) (restrict zdd2 (k,True)) where
    zdd2  = zdds0Of (announce kns ags form1) form2
    (P k) = freshp props

zdds0Of kns@(KnSZs0 props _ _) (AnnounceW ags form1 form2) =
  ifthenelse (zdds0Of kns form1) zdd2a zdd2b where
    zdd2a = restrict (zdds0Of (announce kns ags form1) form2) (k,True)
    zdd2b = restrict (zdds0Of (announce kns ags form1) form2) (k,False)
    (P k) = freshp props

zdds0Of kns (PubAnnounce form1 form2) = imp (zdds0Of kns form1) newform2 where
    newform2 = zdds0Of (pubAnnounce kns form1) form2

zdds0Of kns (PubAnnounceW form1 form2) =
  ifthenelse (zdds0Of kns form1) newform2a newform2b where
    newform2a = zdds0Of (pubAnnounce kns form1) form2
    newform2b = zdds0Of (pubAnnounce kns (Neg form1)) form2

zdds0Of _ (Dia _ _) = error "Dynamic operators are not implemented for CUDD."
zdds0Of _ _ = error "zdds0Of with a wrong kns type"

--ZDD in f0s1 form

boolZddf0Of :: Form -> Dd Z
boolZddf0Of Top           = botZ 
boolZddf0Of Bot           = topZ 
boolZddf0Of (PrpF (P n))  = neg (varZ n)
boolZddf0Of (Neg (PrpF (P n)))    = varZ n
boolZddf0Of (Neg form)    = neg (boolZddf0Of form)
boolZddf0Of (Conj forms)  = disSet $ map boolZddf0Of forms
boolZddf0Of (Disj forms)  = conSet $ map boolZddf0Of forms
boolZddf0Of (Impl f g)    = imp (boolZddf0Of g) (boolZddf0Of f) 
boolZddf0Of (Equi f g)    = equ (boolZddf0Of f) (boolZddf0Of g)
boolZddf0Of (Forall ps f) = existsSet (map fromEnum ps) (boolZddf0Of f)
boolZddf0Of (Exists ps f) = forallSet (map fromEnum ps) (boolZddf0Of f)
boolZddf0Of _             = error "boolZddf0Of failed: Not a boolean formula."

zddf0Of :: KnowStruct -> Form -> Dd Z
zddf0Of _   Top           = botZ 
zddf0Of _   Bot           = topZ 
zddf0Of _   (PrpF (P n))  = neg (varZ n)
zddf0Of _   (Neg (PrpF (P n)))    = varZ n
zddf0Of kns (Neg form) = neg (zddf0Of kns form)

zddf0Of kns (Conj forms)  = disSet $ map (zddf0Of kns) forms
zddf0Of kns (Disj forms)  = conSet $ map (zddf0Of kns) forms
zddf0Of kns (Xor  forms)  = xorSet $ map (zddf0Of kns) forms

zddf0Of kns (Impl f g)    = imp (zddf0Of kns g) (zddf0Of kns f)
zddf0Of kns (Equi f g)    = equ (zddf0Of kns f) (zddf0Of kns g)

zddf0Of kns (Forall ps f) = existsSet (map fromEnum ps) (zddf0Of kns f)
zddf0Of kns (Exists ps f) = forallSet (map fromEnum ps) (zddf0Of kns f)

zddf0Of kns@(KnSZf0 allprops lawzdd obs) (K i form) =
  forallSet otherps (imp lawzdd (zddf0Of kns form)) where
    otherps = map (\(P n) -> n) $ allprops \\ apply obs i

zddf0Of kns@(KnSZf0 allprops lawzdd obs) (Kw i form) =
  disSet [ forallSet otherps (imp lawzdd (zddf0Of kns f)) | f <- [form, Neg form] ] where
    otherps = map (\(P n) -> n) $ allprops \\ apply obs i

zddf0Of kns@(KnSZf0 allprops lawzdd obs) (Ck ags form) = gfpZ lambda where
  lambda z = conSet $ zddf0Of kns form : [ forallSet (otherps i) (imp lawzdd z) | i <- ags ]
  otherps i = map (\(P n) -> n) $ allprops \\ apply obs i

zddf0Of kns (Ckw ags form) = dis (zddf0Of kns (Ck ags form)) (zddf0Of kns (Ck ags (Neg form)))

zddf0Of kns@(KnSZf0 props _ _) (Announce ags form1 form2) =
  imp (zddf0Of kns form1) (restrict zdd2 (k,True)) where
    zdd2  = zddf0Of (announce kns ags form1) form2
    (P k) = freshp props

zddf0Of kns@(KnSZf0 props _ _) (AnnounceW ags form1 form2) =
  ifthenelse (zddf0Of kns form1) zdd2a zdd2b where
    zdd2a = restrict (zddf0Of (announce kns ags form1) form2) (k,True)
    zdd2b = restrict (zddf0Of (announce kns ags form1) form2) (k,False)
    (P k) = freshp props

zddf0Of kns (PubAnnounce form1 form2) = imp (zddf0Of kns form1) newform2 where
    newform2 = zddf0Of (pubAnnounce kns form1) form2

zddf0Of kns (PubAnnounceW form1 form2) =
  ifthenelse (zddf0Of kns form1) newform2a newform2b where
    newform2a = zddf0Of (pubAnnounce kns form1) form2
    newform2b = zddf0Of (pubAnnounce kns (Neg form1)) form2

zddf0Of _ (Dia _ _) = error "Dynamic operators are not implemented for CUDD."
zddf0Of _ _ = error "zddf0Of with a wrong kns type"

--ZDD in f0s0 form

boolZddf0s0Of :: Form -> Dd Z
boolZddf0s0Of Top           = botZ 
boolZddf0s0Of Bot           = topZ 
boolZddf0s0Of (PrpF (P n))  = varZ n -- double swap makes it normal
boolZddf0s0Of (Neg form)    = neg (boolZddf0s0Of form)
boolZddf0s0Of (Conj forms)  = disSet $ map boolZddf0s0Of forms
boolZddf0s0Of (Disj forms)  = conSet $ map boolZddf0s0Of forms
boolZddf0s0Of (Impl f g)    = imp (boolZddf0s0Of g) (boolZddf0s0Of f)
boolZddf0s0Of (Equi f g)    = equ (boolZddf0s0Of f) (boolZddf0s0Of g)
boolZddf0s0Of (Forall ps f) = existsSet (map fromEnum ps) (boolZddf0s0Of f)
boolZddf0s0Of (Exists ps f) = forallSet  (map fromEnum ps) (boolZddf0s0Of f)
boolZddf0s0Of _             = error "boolZddf0s0Of failed: Not a boolean formula."

zddf0s0Of :: KnowStruct -> Form -> Dd Z
zddf0s0Of _   Top           = botZ  
zddf0s0Of _   Bot           = topZ  
zddf0s0Of _   (PrpF (P n))  = varZ n 
zddf0s0Of kns (Neg form) = neg (zddf0s0Of kns form)

zddf0s0Of kns (Conj forms)  = disSet $ map (zddf0s0Of kns) forms
zddf0s0Of kns (Disj forms)  = conSet $ map (zddf0s0Of kns) forms
zddf0s0Of kns (Xor  forms)  = xorSet $ map (zddf0s0Of kns) forms --euh improve this one

zddf0s0Of kns (Impl f g)    = imp (zddf0s0Of kns g) (zddf0s0Of kns f) 
zddf0s0Of kns (Equi f g)    = equ (zddf0s0Of kns f) (zddf0s0Of kns g)

zddf0s0Of kns (Forall ps f) = existsSet (map fromEnum ps) (zddf0s0Of kns f) --ofcourse also these
zddf0s0Of kns (Exists ps f) = forallSet (map fromEnum ps) (zddf0s0Of kns f)

zddf0s0Of kns@(KnSZf0s0 allprops lawzdd obs) (K i form) =
  forallSet otherps (imp lawzdd (zddf0s0Of kns form)) where
    otherps = map (\(P n) -> n) $ allprops \\ apply obs i

zddf0s0Of kns@(KnSZf0s0 allprops lawzdd obs) (Kw i form) =
  disSet [ forallSet otherps (imp lawzdd (zddf0s0Of kns f)) | f <- [form, Neg form] ] where
    otherps = map (\(P n) -> n) $ allprops \\ apply obs i

zddf0s0Of kns@(KnSZf0s0 allprops lawzdd obs) (Ck ags form) = gfpZ lambda where
  lambda z = conSet $ zddf0s0Of kns form : [ forallSet (otherps i) (imp lawzdd z) | i <- ags ]
  otherps i = map (\(P n) -> n) $ allprops \\ apply obs i

zddf0s0Of kns (Ckw ags form) = dis (zddf0s0Of kns (Ck ags form)) (zddf0s0Of kns (Ck ags (Neg form)))

zddf0s0Of kns@(KnSZf0s0 props _ _) (Announce ags form1 form2) =
  imp (zddf0s0Of kns form1) (restrict zdd2 (k,True)) where
    zdd2  = zddf0s0Of (announce kns ags form1) form2
    (P k) = freshp props

zddf0s0Of kns@(KnSZf0s0 props _ _) (AnnounceW ags form1 form2) =
  ifthenelse (zddf0s0Of kns form1) zdd2a zdd2b where
    zdd2a = restrict (zddf0s0Of (announce kns ags form1) form2) (k,True)
    zdd2b = restrict (zddf0s0Of (announce kns ags form1) form2) (k,False)
    (P k) = freshp props

zddf0s0Of kns (PubAnnounce form1 form2) = imp (zddf0s0Of kns form1) newform2 where
    newform2 = zddf0s0Of (pubAnnounce kns form1) form2

zddf0s0Of kns (PubAnnounceW form1 form2) =
  ifthenelse (zddf0s0Of kns form1) newform2a newform2b where
    newform2a = zddf0s0Of (pubAnnounce kns form1) form2
    newform2b = zddf0s0Of (pubAnnounce kns (Neg form1)) form2

zddf0s0Of _ (Dia _ _) = error "Dynamic operators are not implemented for CUDD."
zddf0s0Of _ _ = error "zddf0s0Of with a wrong kns type"


--Converting between BDD and ZDDs, and other supportive functions

convertTestZdd :: KnowStruct -> Form -> Bool 
convertTestZdd kns@(KnS _ law _) query = unsafePerformIO $ do
  let q = createZddFromBdd (bddOf kns query)
  let l = createZddFromBdd law
  let r = l `imp` q
  return (r == topZ)
convertTestZdd _ _ = error "wrong knowstruct type or query given in convertTestZdd"


convertToZdd :: KnowStruct -> KnowStruct
convertToZdd (KnS vocab law obs) = KnSZ vocab (createZddFromBdd law) obs
convertToZdd kns@(KnSZ _ _ _ ) = kns
convertToZdd (KnSZs0 vocab law obs) = KnSZ vocab (neg law) obs
convertToZdd (KnSZf0 vocab law obs) = KnSZ vocab (complementZ law) obs
convertToZdd (KnSZf0s0 vocab law obs) = KnSZ vocab (complementZ $ neg law) obs

convertToZdds0 :: KnowStruct -> KnowStruct
convertToZdds0 (KnS vocab law obs) = KnSZs0 vocab (neg $ createZddFromBdd law) obs
convertToZdds0 (KnSZ vocab law obs) = KnSZs0 vocab (neg law) obs
convertToZdds0 kns@(KnSZs0 _ _ _) = kns
convertToZdds0 (KnSZf0 vocab law obs) = KnSZs0 vocab (complementZ $ neg law) obs
convertToZdds0 (KnSZf0s0 vocab law obs) = KnSZs0 vocab (complementZ law) obs

convertToZddf0 :: KnowStruct -> KnowStruct
convertToZddf0 (KnS vocab law obs) = KnSZf0 vocab (complementZ $ createZddFromBdd law) obs
convertToZddf0 (KnSZ vocab law obs) = KnSZf0 vocab (complementZ law) obs
convertToZddf0 (KnSZs0 vocab law obs) = KnSZf0 vocab (complementZ $ neg law) obs
convertToZddf0 kns@(KnSZf0 _ _ _ ) = kns 
convertToZddf0 (KnSZf0s0 vocab law obs) = KnSZf0 vocab (neg law) obs

convertToZddf0s0 :: KnowStruct -> KnowStruct
convertToZddf0s0 (KnS vocab law obs) = KnSZf0s0 vocab (complementZ $ neg $ createZddFromBdd law) obs
convertToZddf0s0 (KnSZ vocab law obs) = KnSZf0s0 vocab (complementZ $ neg law) obs
convertToZddf0s0 (KnSZs0 vocab law obs) = KnSZf0s0 vocab (complementZ law) obs
convertToZddf0s0 (KnSZf0 vocab law obs) = KnSZf0s0 vocab (neg law) obs
convertToZddf0s0 kns@(KnSZf0s0 _ _ _) = kns

initZddVars :: [Int] -> IO()
initZddVars vocab = do
  let v = initZddVarsWithInt vocab
  _ <- return $! rnf (forceCheckDd v)
  return ()

--portvar :: IO() --Sets the BDD vars as ZDD vars
--portvar = portVars




--------------Debugging!


{-mudScnInit :: Int -> Int -> KnowScene
mudScnInit n m = (KnS vocab law obs, actual) where
  vocab  = [P 1 .. P n]
  law    = boolBddOf Top
  obs    = [ (show i, delete (P i) vocab) | i <- [1..n] ]
  actual = [P 1 .. P m]-}


giveDebugTex :: String
giveDebugTex = concat [
  "Testing.\\\\ \n"
  --,ns, ": \\\\ \\[", giveZddTex n, "\\] \\\\ \n"
  --,ms, ": \\\\ \\[", giveZddTex m, "\\] \\\\ \n"
  --,as, ": \\\\ \\[", giveBddTex a, "\\] \\\\ \n"
  --,bs, ": \\\\ \\[", giveZddTex b, "\\] \\\\ \n"
  --,cs, ": \\\\ \\[", giveZddTex c, "\\] \\\\ \n"
  --,ds, ": \\\\ \\[", giveZddTex d, "\\] \\\\ \n"
  ,d2s, ": \\\\ \\[", giveZddTex d2, "\\] \\\\ \n"
  --,es, ": \\\\ \\[", giveZddTex e, "\\] \\\\ \n"
  ,e2s, ": \\\\ \\[", giveZddTex e2, "\\] \\\\ \n"
  ,fs, ": \\\\ \\[", giveZddTex f, "\\] \\\\ \n"
  ,gs, ": \\\\ \\[", giveZddTex g, "\\] \\\\ \n"
  ,hs, ": \\\\ \\[", giveZddTex h, "\\] \\\\ \n"
  ,is, ": \\\\ \\[", giveZddTex i, "\\] \\\\ \n"
  ,js, ": \\\\ \\[", giveZddTex j, "\\] \\\\ \n"
  ,ks, ": \\\\ \\[", giveZddTex k, "\\] \\\\ \n"
  --,js, ": \\\\ \\[", giveZddTex j, "\\] \\\\ \n"
  --,f2s, ": \\\\ \\[", giveZddTex f2, "\\] \\\\ \n"
  --,ys, ": \\\\ \\[", giveZddTex y, "\\] \\\\ \n"
  --,zs, ": \\\\ \\[", giveZddTex z, "\\] \\\\ \n"
  --,z2s, ": \\\\ \\[", giveZddTex z2, "\\] \\\\ \n"
  --
  -- add comparisonTestZddVsBdd here for comparing evaluations
  --, comparisonTestZddVsBdd
  --
  ] where
    --for zdd use topZ, botZ and varZ instead
    --
    --cudd printing of trees has some quirks:
    --it has 3 lines: solid (true), dashed(false), dotted(straight to zero, i think)
    --the uppermost square node represents the group (used in zdd-bdd-add combinations)
    --some nodes have a boundary others dont (i think it has to do with negations in bdds)
    --cudd starts from var 0 thus the printed variables are all -1
    --
    --ms = "sub0 (2 and neg 3) 4"
    --m = sub0 (varZ 2 `con` neg (varZ 3)) 4
    --ns = "product  (sub0 (2 and neg 3) 4) neg (1 con 2 con 3)"
    --n = productZ (sub0 (varZ 2 `con` neg (varZ 3)) 4) $ varZ 4--neg (varZ 1 `con` varZ 2 `con` varZ 3)

    --is = "only both var 3"
    --i = onlyBothVarZ 3
    --js = "only neg var 3"
    --j = onlyNotVarZ 3

    --as = "BDD: (exists 1 ((neg 1 imp ( neg 3) con 2 imp (neg 3)))"
    --a = exists 1 ((neg $ var 1 `imp` ( neg $ var 3)) `con` (var 2 `imp` (neg $ var 3 )))
    --bs = "ZDD Conversion: (exists 1 ((neg 1 imp ( neg 3) con 2 imp (neg 3)))"
    --b = createZddFromBdd (exists 1 ((neg $ var 1 `imp` ( neg $ var 3)) `con` (var 2 `imp` (neg $ var 3 ))))
    --cs = "ZDD: (exists 1 ((neg 1 imp ( neg 3) con 2 imp (neg 3)))"
    --c = exists 1 ((neg $ varZ 1 `imp` ( neg $ varZ 3)) `con` (varZ 2 `imp` (neg $ varZ 3 )))

    ds = "ZDD: sub0 ((neg 1 imp ( neg 3)) con 2 imp (neg 3))"
    d = sub0 ((neg $ varZ 1 `imp` ( neg $ varZ 3)) `con` (varZ 2 `imp` (neg $ varZ 3 ))) 1 
    es = "ZDD: product 1 (sub0 ((neg 1 imp ( neg 3)) con 2 imp (neg 3))"
    e = productZ (sub0 ((neg $ varZ 1 `imp` ( neg $ varZ 3)) `con` (varZ 2 `imp` (neg $ varZ 3 ))) 1 ) (onlyNotVarZ 1)
    d2s = "ZDD: sub1 ((neg 1 imp ( neg 3)) con 2 imp (neg 3))"
    d2 = sub1 (((neg $ varZ 1) `imp` ( neg $ varZ 3)) `con` (varZ 2 `imp` (neg $ varZ 3 ))) 1 
    e2s = "ZDD: product 1 (sub1 ((neg 1 imp ( neg 3)) con 2 imp (neg 3))"
    e2 = productZ (sub1 (((neg $ varZ 1) `imp` ( neg $ varZ 3)) `con` (varZ 2 `imp` (neg $ varZ 3 ))) 1 ) (onlyNotVarZ 1)
    
    fs = "ZDD: (neg 1 imp ( neg 3)) con 2 imp (neg 3)"
    f = (((neg $ varZ 1) `imp` ( neg $ varZ 3)) `con` (varZ 2 `imp` (neg $ varZ 3 )))
    gs = "ZDD Conv: (neg 1 imp ( neg 3)) con 2 imp (neg 3)"
    g = createZddFromBdd (((neg $ var 1) `imp` ( neg $ var 3)) `con` (var 2 `imp` (neg $ var 3 )))
    --hs = "ZDD: (neg 1 imp ( neg 3))" 
    --h = ((neg $ varZ 1) `imp` ( neg $ varZ 3))
    --is = "ZDD Conv: (neg 1 imp ( neg 3))"
    --i = createZddFromBdd ((neg $ var 1) `imp` ( neg $ var 3))
    --js = "ZDD: 2 imp (neg 3)" 
    --j = varZ 2 `imp` (neg $ varZ 3 )
    --ks = "ZDD Conv: 2 imp (neg 3)"
    --k = createZddFromBdd (var 2 `imp` (neg $ var 3 ))
{-}Exists 1 ((~ 1 -> ~3) & (2 -> ~3))

    --convert to ZDDs0f0
    as = "BDD: 4 imp (neg 1 con neg 3) con 2 imp (3 or 4)"
    a = (var 4 `imp` (neg ( var 1) `con` neg ( var 3))) `con` (var 2 `imp` (var 3 or var 4))
    bs = "ZDD"
    b = (varZ 4 `imp` (neg ( varZ 1) `con` neg ( varZ 3))) `con` (varZ 2 `imp` (varZ 3 or varZ 4))
    cs = "ZDDs0"
    c = ((neg varZ 4) `imp` (varZ 1 `con` varZ 3)) `con` ((neg varZ 2) `imp` ((neg varZ 3) or (neg varZ 4)))
    ds = "ZDDf0"
    d = (varZ 4 `imp` (neg ( varZ 1) `con` neg ( varZ 3))) `con` (varZ 2 `imp` (varZ 3 or varZ 4))
    es = "ZDDs0f0"
    e = (varZ 4 `imp` (neg ( varZ 1) `con` neg ( varZ 3))) `con` (varZ 2 `imp` (varZ 3 or varZ 4))

    --es = "exists\\_2 (neg 3 con 2)"
    --e = exists 2 (neg (varZ 3) `con` varZ 2)
    fs = "ConvertZDD"
    f = exists 2 (neg ( var 3) `con` var 2)
    f2s = "ConvertZDDs0"
    f2 = createZddFromBdd (exists 2 (neg (var 3) `con` var 2))
    ys = "ConvertZDDf0"
    y = forall 2 (neg (neg (varZ 3) `con` varZ 2))
    zs = "ConvertZDDf0s0"
    z = forall 2 (neg (neg (var 3) `con` var 2))-}


{-comparisonTestZddVsBdd :: String
comparisonTestZddVsBdd = concat [
  "Comparison test on queries: \\\\ \n"
  , "exists zdd equal to bdd, on (E2(3) -\\> 3): " ++ show ((a == top) == (b == topZ)) ++ "\\\\ \n"
  , "forall zdd equal to bdd, on (A2(3) -\\> 3):" ++ show ((c == top) == (d == topZ)) ++ "\\\\ \n"
  , "empty zdd equal to botZ, on (A2(3) -\\> 3):" ++ show (e == botZ) ++ "\\\\ \n"
  ] where
    a = exists 2 (var 3) `imp` var 3
    b = exists 2 (varZ 3) `imp` varZ 3
    c = forall 2 (var 3) `imp` var 3
    d = forall 2 (varZ 3) `imp` varZ 3
    e = neg (varZ 4 `con` (varZ 3 `con` (varZ 2 `con` varZ 1)))-}


    
--------------------------- Texable functionality


texDdBWith :: Dd B -> [Prp] -> String 
texDdBWith d vocab = unsafePerformIO $ do
  (i,o,_,_) <- runInteractiveCommand "dot2tex --figpreamble=\"\\huge\" --figonly -traw"
  
  let xDotText = B.pack $ returnDot d
  let myShow = formatDotCUDD vocab -- currently uses P1 .. Pn for names of variables 1 .. n, can be changed when the parser accepts non number propositions
  let xDotGraph = parseDotGraphLiberally xDotText :: DotGen.DotGraph String
  let renamedXDotGraph = renameMyGraph xDotGraph myShow  

  hPutStr i (B.unpack (renderDot $ toDot renamedXDotGraph) ++ "\n")  
  hClose i
  result <- hGetContents o
  return $ dropWhileEnd isSpace $ dropWhile isSpace result

texDdZWith :: Dd Z -> [Prp] -> String 
texDdZWith d vocab = unsafePerformIO $ do
  (i,o,_,_) <- runInteractiveCommand "dot2tex --figpreamble=\"\\huge\" --figonly -traw"
  
  let xDotText = B.pack $ returnDot d
  let myShow = formatDotCUDD vocab -- currently uses P1 .. Pn for names of variables 1 .. n, can be changed when the parser accepts non number propositions
  let xDotGraph = parseDotGraphLiberally xDotText :: DotGen.DotGraph String
  let renamedXDotGraph = renameMyGraph xDotGraph myShow  

  hPutStr i (B.unpack (renderDot $ toDot renamedXDotGraph) ++ "\n")  
  hClose i
  result <- hGetContents o
  return $ dropWhileEnd isSpace $ dropWhile isSpace result

texDdB :: Dd B -> String 
texDdB d = unsafePerformIO $ do
  (i,o,_,_) <- runInteractiveCommand "dot2tex --figpreamble=\"\\huge\" --figonly -traw"
  writeToDot d "tempDD.dot"
  xDotText <- readFile "tempDD.dot"
  hPutStr i (xDotText)
  --let xDotGraph = parseDotGraphLiberally (B.pack xDotText) :: DotGen.DotGraph String
  --hPutStr i ("warning, use texDdBWith for correct variable names: " ++ B.unpack (renderDot $ toDot xDotGraph) ++ "\n")
  hClose i
  result <- hGetContents o
  return $ dropWhileEnd isSpace $ dropWhile isSpace result

texDdZ :: Dd Z -> String
texDdZ d = unsafePerformIO $ do
  (i,o,_,_) <- runInteractiveCommand "dot2tex --figpreamble=\"\\huge\" --figonly -traw"
  writeToDot d "tempDD.dot"
  xDotText <- readFile "tempDD.dot"
  hPutStr i (xDotText)
  --let xDotGraph = parseDotGraphLiberally (B.pack xDotText) :: DotGen.DotGraph String
  --hPutStr i ("warning, use texDdBWith for correct variable names: " ++ B.unpack (renderDot $ toDot xDotGraph) ++ "\n")
  hClose i
  result <- hGetContents o
  return $ dropWhileEnd isSpace $ dropWhile isSpace result

renameMyGraph :: DotGen.DotGraph String -> [(String, String)] -> DotGen.DotGraph String
renameMyGraph dg myShow =
  dg { DotGen.graphStatements = fmap changeGraphStatement (DotGen.graphStatements dg) } where
    changeGraphStatement gs = case gs of
      DotGen.SG sg -> DotGen.SG (sg {DotGen.subGraphStmts = fmap renameNodeNames (DotGen.subGraphStmts sg)}) where
        renameNodeNames sgStmt = case sgStmt of
          DotGen.DN dn -> DotGen.DN (renameNode dn myShow)
          DotGen.DE de -> DotGen.DE (renameEdge de myShow)
          x -> x
      DotGen.DE de -> DotGen.DE (renameEdge de myShow)
      x -> x

renameNode :: DotGen.DotNode String -> [(String, String)] -> DotGen.DotNode String
renameNode dn myShow = case lookup (DotGen.nodeID dn) myShow of
  (Just v) -> dn { nodeID = v } --nodeID is in myShow, thus replace the Int with the proposition
  Nothing -> dn --otherwise do nothing


renameEdge :: DotGen.DotEdge String -> [(String, String)] -> DotGen.DotEdge String
-- replace also the node name occurences in the edge statements
renameEdge de myShow = changeFromNode (changeToNode de) where
  changeToNode edge = case lookup (DotGen.toNode edge) myShow of
    (Just v) -> edge {toNode = v }
    Nothing -> edge
  changeFromNode edge = case lookup (DotGen.fromNode edge) myShow of
    (Just v) -> edge {fromNode = v }
    Nothing -> edge

formatDotCUDD :: [Prp] -> [(String, String)]
formatDotCUDD = map propToString where
  propToString p = (" " ++ show (fromEnum p - 1) ++ " ", "p" ++ show (fromEnum p))

instance TexAble KnowStruct where
  tex (KnS props lawbdd obs) = concat
    [ " \\left( \n"
    , tex props ++ ", "
    , " \\begin{array}{l} \\scalebox{0.4}{"
    , texDdBWith lawbdd props
    , "} \\end{array}\n "
    , ", \\begin{array}{l}\n"
    , intercalate " \\\\\n " (map (\(_,os) -> tex os) obs)
    , "\\end{array}\n"
    , " \\right)" ]
  tex (KnSZ props lawzdd obs) = concat
    [ " \\left( \n"
    , tex props ++ ", "
    , " \\begin{array}{l} \\scalebox{0.4}{"
    , texDdZWith lawzdd props
    , "} \\end{array}\n "
    , ", \\begin{array}{l}\n"
    , intercalate " \\\\\n " (map (\(_,os) -> tex os) obs)
    , "\\end{array}\n"
    , " \\right)" ]
  tex (KnSZs0 props lawzdd obs) = concat
    [ " \\left( \n"
    , tex props ++ ", "
    , " \\begin{array}{l} \\scalebox{0.4}{"
    , texDdZWith lawzdd props
    , "} \\end{array}\n "
    , ", \\begin{array}{l}\n"
    , intercalate " \\\\\n " (map (\(_,os) -> tex os) obs)
    , "\\end{array}\n"
    , " \\right)" ]
  tex (KnSZf0 props lawzdd obs) = concat
    [ " \\left( \n"
    , tex props ++ ", "
    , " \\begin{array}{l} \\scalebox{0.4}{"
    , texDdZWith lawzdd props
    , "} \\end{array}\n "
    , ", \\begin{array}{l}\n"
    , intercalate " \\\\\n " (map (\(_,os) -> tex os) obs)
    , "\\end{array}\n"
    , " \\right)" ]
  tex (KnSZf0s0 props lawzdd obs) = concat
    [ " \\left( \n"
    , tex props ++ ", "
    , " \\begin{array}{l} \\scalebox{0.4}{"
    , texDdZWith lawzdd props
    , "} \\end{array}\n "
    , ", \\begin{array}{l}\n"
    , intercalate " \\\\\n " (map (\(_,os) -> tex os) obs)
    , "\\end{array}\n"
    , " \\right)" ]


instance TexAble KnowScene where
  tex (kns, state) = tex kns ++ " , " ++ tex state

giveZddTex :: Dd Z -> String
giveZddTex z = concat 
  [
    " \\begin{array}{l} \\scalebox{0.4}{"
    , texDdZ z
    , "} \\end{array}\n "] 
  
giveBddTex :: Dd B -> String
giveBddTex b = concat 
  [
    " \\begin{array}{l} \\scalebox{0.4}{"
    , texDdB b
    , "} \\end{array}\n "]







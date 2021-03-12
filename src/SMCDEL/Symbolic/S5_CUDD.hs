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
validViaDd kns@(KnSZ _ lawzdd _) f = topZ == lawzdd `imp` ddOf kns f
validViaDd kns@(KnSZs0 _ lawzdd _) f = topZ == lawzdd `imp` ddOf kns f
validViaDd kns@(KnSZf0 _ lawzdd _) f = botZ == lawzdd `impf0` ddOf kns f
validViaDd kns@(KnSZf0s0 _ lawzdd _) f = botZ == lawzdd `impf0` ddOf kns f 

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
       | otherwise = error ("evalViaDd failed: ZDD leftover:\n" ++ (texDdZ z))
  z    = restrictSetQ (ddOf kns f) allprops list
  list = [ (n, P n `elem` s) | (P n) <- allprops ]
evalViaDd (kns@(KnSZs0 allprops _ _),s) f = bool where 
  bool | z==topZ = True
       | z==botZ = False
       | otherwise = error ("evalViaDd failed: ZDDs0 leftover:\n" ++ show z) --make this show return var int from cudd
  z    = restrictSetQs0(ddOf kns f) allprops list
  list = [ (n, P n `elem` s) | (P n) <- allprops ] 
evalViaDd (kns@(KnSZf0 allprops _ _),s) f = bool where
  bool | z==botZ = True
       | z==topZ = False
       | otherwise = error ("evalViaDd failed: ZDDf0 leftover:\n" ++ show z)
  z    = restrictSetQ(ddOf kns f) allprops list
  list = [ (n, P n `elem` s) | (P n) <- allprops ]
evalViaDd (kns@(KnSZf0s0 allprops _ _),s) f = bool where 
  bool | z==botZ = True
       | z==topZ = False
       | otherwise = error ("evalViaDd failed: ZDDf0s0 leftover:\n" ++ show z)
  z    = restrictSetQs0 (ddOf kns f) allprops list
  list = [ (n, P n `elem` s) | (P n) <- allprops ]


-- Transformations acting on knowledge structs (PAL)

pubAnnounce :: KnowStruct -> Form -> KnowStruct
pubAnnounce kns@(KnS props lawbdd obs) psi = KnS props newlawbdd obs where
  newlawbdd = con lawbdd (bddOf kns psi)
pubAnnounce kns@(KnSZ props lawzdd obs) psi = KnSZ props newlawzdd obs where
  newlawzdd = con lawzdd (ddOf kns psi)
pubAnnounce kns@(KnSZs0 props lawzdd obs) psi = KnSZs0 props newlawzdd obs where
  newlawzdd = con lawzdd (ddOf kns psi)
pubAnnounce kns@(KnSZf0 props lawzdd obs) psi = KnSZf0 props newlawzdd obs where
  newlawzdd = dis lawzdd (ddOf kns psi)
pubAnnounce kns@(KnSZf0s0 props lawzdd obs) psi = KnSZf0s0 props newlawzdd obs where
  newlawzdd = dis lawzdd (ddOf kns psi)

announce :: KnowStruct -> [Agent] -> Form -> KnowStruct
announce kns@(KnS props lawbdd obs) ags psi = KnS newprops newlawbdd newobs where
  proppsi@(P k) = freshp props
  newprops  = proppsi:props
  newlawbdd = con lawbdd (equ (var k) (bddOf kns psi))
  newobs    = [(i, apply obs i ++ [proppsi | i `elem` ags]) | i <- map fst obs]

announce kns@(KnSZ props lawzdd obs) ags psi = KnSZ newprops newlawzdd newobs where
  proppsi@(P k) = freshp props
  newprops  = proppsi:props
  newlawzdd = con lawzdd (equ (varZ k) (ddOf kns psi))
  newobs    = [(i, apply obs i ++ [proppsi | i `elem` ags]) | i <- map fst obs]
announce kns@(KnSZs0 props lawzdd obs) ags psi = KnSZs0 newprops newlawzdd newobs where
  proppsi@(P k) = freshp props
  newprops  = proppsi:props
  newlawzdd = con lawzdd (equ (varZ k) (ddOf kns psi))
  newobs    = [(i, apply obs i ++ [proppsi | i `elem` ags]) | i <- map fst obs]

--should i invert this under f0?
announce kns@(KnSZf0 props lawzdd obs) ags psi = KnSZs0 newprops newlawzdd newobs where
  proppsi@(P k) = freshp props
  newprops  = proppsi:props
  newlawzdd = dis lawzdd (equ (varZ k) (ddOf kns psi))
  newobs    = [(i, apply obs i ++ [proppsi | i `elem` ags]) | i <- map fst obs]
announce kns@(KnSZf0s0 props lawzdd obs) ags psi = KnSZs0 newprops newlawzdd newobs where
  proppsi@(P k) = freshp props
  newprops  = proppsi:props
  newlawzdd = dis lawzdd (equ (varZ k) (ddOf kns psi))
  newobs    = [(i, apply obs i ++ [proppsi | i `elem` ags]) | i <- map fst obs]





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


boolZddOf :: [Prp] -> Form -> Dd Z
boolZddOf _ Top            = topZ
boolZddOf _ Bot            = botZ
boolZddOf _ (PrpF (P n))   = varZ n
boolZddOf c (Neg form)     = neg (boolZddOf c form)
boolZddOf c (Conj forms)   = conSet $ map (boolZddOf c) forms 
boolZddOf c (Disj forms)   = disSet $ map (boolZddOf c) forms 
boolZddOf c (Impl f g)     = imp (boolZddOf c f) (boolZddOf c g)
boolZddOf c (Equi f g)     = equ (boolZddOf c f) (boolZddOf c g)
boolZddOf c (Forall ps f)  = forallSetQ (map fromEnum ps) c (boolZddOf c f)
boolZddOf c (Exists ps f)  = existsSetQ (map fromEnum ps) c (boolZddOf c f)
boolZddOf _             _ = error "boolZddOf failed: Not a boolean formula."

boolZdds0Of :: [Prp] -> Form -> Dd Z
boolZdds0Of _ Top           = topZ
boolZdds0Of _ Bot           = botZ
boolZdds0Of _ (PrpF (P n))  = neg (varZ n)
boolZdds0Of _ (Neg (PrpF (P n)))    = varZ n
boolZdds0Of c (Neg form)    = neg (boolZdds0Of c form)
boolZdds0Of c (Conj forms)  = conSet $ map (boolZdds0Of c) forms
boolZdds0Of c (Disj forms)  = disSet $ map (boolZdds0Of c) forms
boolZdds0Of c (Impl f g)    = imp (boolZdds0Of c f) (boolZdds0Of c g)
boolZdds0Of c (Equi f g)    = equ (boolZdds0Of c f) (boolZdds0Of c g)
boolZdds0Of c (Forall ps f) = forallSetQ (map fromEnum ps) c (boolZdds0Of c f)
boolZdds0Of c (Exists ps f) = existsSetQ (map fromEnum ps) c (boolZdds0Of c f)
boolZdds0Of _ _             = error "boolZdds0Of failed: Not a boolean formula."


boolZddf0Of :: [Prp] -> Form -> Dd Z
boolZddf0Of _ Top           = botZ 
boolZddf0Of _ Bot           = topZ 
boolZddf0Of _ (PrpF (P n))  = varZ n
boolZddf0Of c (Neg form)    = neg (boolZddf0Of c form)
boolZddf0Of c (Conj forms)  = disSet $ map (boolZddf0Of c) forms
boolZddf0Of c (Disj forms)  = conSet $ map (boolZddf0Of c) forms
boolZddf0Of c (Impl f g)    = impf0 (boolZddf0Of c f) (boolZddf0Of c g) 
boolZddf0Of c (Equi f g)    = equf0 (boolZddf0Of c g) (boolZddf0Of c f)
boolZddf0Of c (Forall ps f) = existsSetQ (map fromEnum ps) c (boolZddf0Of c f)
boolZddf0Of c (Exists ps f) = forallSetQ (map fromEnum ps) c (boolZddf0Of c f)
boolZddf0Of _ _             = error "boolZddf0Of failed: Not a boolean formula."

boolZddf0s0Of :: [Prp] -> Form -> Dd Z
boolZddf0s0Of _ Top           = botZ 
boolZddf0s0Of _ Bot           = topZ 
boolZddf0s0Of _ (PrpF (P n))  = neg (varZ n)
boolZddf0s0Of _ (Neg (PrpF (P n)))    = varZ n
boolZddf0s0Of c (Neg form)    = neg (boolZddf0s0Of c form)
boolZddf0s0Of c (Conj forms)  = disSet $ map (boolZddf0s0Of c) forms
boolZddf0s0Of c (Disj forms)  = conSet $ map (boolZddf0s0Of c) forms
boolZddf0s0Of c (Impl f g)    = impf0 (boolZddf0s0Of c f) (boolZddf0s0Of c g) 
boolZddf0s0Of c (Equi f g)    = equf0 (boolZddf0s0Of c f) (boolZddf0s0Of c g)
boolZddf0s0Of c (Forall ps f) = existsSetQ (map fromEnum ps) c (boolZddf0s0Of c f)
boolZddf0s0Of c (Exists ps f) = forallSetQ (map fromEnum ps) c (boolZddf0s0Of c f)
boolZddf0s0Of _ _             = error "boolZddf0s0Of failed: Not a boolean formula."


ddOf :: KnowStruct -> Form -> Dd Z

-- allversions

-- ZDD version
ddOf (KnSZ _ _ _) Top           = topZ
ddOf (KnSZ _ _ _)    Bot           = botZ
ddOf (KnSZ _ _ _)    (PrpF (P n))  = varZ n
ddOf kns@(KnSZ _ _ _)  (Neg form) = neg (ddOf kns form)
ddOf kns@(KnSZ _ _ _) (Conj forms)  = conSet $ map (ddOf kns) forms
ddOf kns@(KnSZ _ _ _) (Disj forms)  = disSet $ map (ddOf kns) forms
ddOf kns@(KnSZ _ _ _) (Xor  forms)  = xorSet $ map (ddOf kns) forms

ddOf kns@(KnSZ _ _ _) (Impl f g)    = imp (ddOf kns f) (ddOf kns g)
ddOf kns@(KnSZ _ _ _) (Equi f g)    = equ (ddOf kns f) (ddOf kns g)

ddOf kns@(KnSZ c _ _) (Forall ps f) = forallSetQ (map fromEnum ps) c (ddOf kns f)
ddOf kns@(KnSZ c _ _) (Exists ps f) = existsSetQ (map fromEnum ps) c (ddOf kns f)

ddOf kns@(KnSZ allprops lawzdd obs) (K i form) =
  forallSetQ otherps allprops (imp lawzdd (ddOf kns form)) where
    otherps = map (\(P n) -> n) $ allprops \\ apply obs i

ddOf kns@(KnSZ allprops lawzdd obs) (Kw i form) =
  disSet [ forallSetQ otherps allprops (imp lawzdd (ddOf kns f)) | f <- [form, Neg form] ] where
    otherps = map (\(P n) -> n) $ allprops \\ apply obs i

ddOf kns@(KnSZ allprops lawzdd obs) (Ck ags form) = gfpZ lambda where
  lambda z = conSet $ ddOf kns form : [ forallSetQ (otherps i) allprops (imp lawzdd z) | i <- ags ]
  otherps i = map (\(P n) -> n) $ allprops \\ apply obs i

ddOf kns@(KnSZ _ _ _) (Ckw ags form) = dis (ddOf kns (Ck ags form)) (ddOf kns (Ck ags (Neg form)))

ddOf kns@(KnSZ props _ _) (Announce ags form1 form2) =
  imp (ddOf kns form1) (restrictQ zdd2 props (k,True)) where
    zdd2  = ddOf (announce kns ags form1) form2
    (P k) = freshp props

ddOf kns@(KnSZ props _ _) (AnnounceW ags form1 form2) =
  ifthenelse (ddOf kns form1) zdd2a zdd2b where
    zdd2a = restrictQ (ddOf (announce kns ags form1) form2) props (k,True)
    zdd2b = restrictQ (ddOf (announce kns ags form1) form2) props (k,False)
    (P k) = freshp props

ddOf kns@(KnSZ _ _ _) (PubAnnounce form1 form2) = imp (ddOf kns form1) newform2 where
    newform2 = ddOf (pubAnnounce kns form1) form2

ddOf kns@(KnSZ _ _ _) (PubAnnounceW form1 form2) =
  ifthenelse (ddOf kns form1) newform2a newform2b where
    newform2a = ddOf (pubAnnounce kns form1) form2
    newform2b = ddOf (pubAnnounce kns (Neg form1)) form2


--ZDD in f1s0 form

ddOf (KnSZs0 _ _ _)   Top           = topZ
ddOf (KnSZs0 _ _ _)   Bot           = botZ
ddOf (KnSZs0 _ _ _)   (PrpF (P n))  = neg (varZ n) -- s0 swaps these
ddOf (KnSZs0 _ _ _) (Neg (PrpF (P n))) = varZ n -- s0 swaps these
ddOf kns@(KnSZs0 _ _ _) (Neg form) = neg (ddOf kns form)

ddOf kns@(KnSZs0 _ _ _) (Conj forms)  = conSet $ map (ddOf kns) forms
ddOf kns@(KnSZs0 _ _ _) (Disj forms)  = disSet $ map (ddOf kns) forms
ddOf kns@(KnSZs0 _ _ _) (Xor  forms)  = xorSet $ map (ddOf kns) forms

ddOf kns@(KnSZs0 _ _ _) (Impl f g)    = imp (ddOf kns f) (ddOf kns g)
ddOf kns@(KnSZs0 _ _ _) (Equi f g)    = equ (ddOf kns f) (ddOf kns g)

ddOf kns@(KnSZs0 c _ _) (Forall ps f) = forallSetQ (map fromEnum ps) c (ddOf kns f)
ddOf kns@(KnSZs0 c _ _) (Exists ps f) = existsSetQ (map fromEnum ps) c (ddOf kns f)

ddOf kns@(KnSZs0 allprops lawzdd obs) (K i form) =
  forallSetQ otherps allprops (imp lawzdd (ddOf kns form)) where
    otherps = map (\(P n) -> n) $ allprops \\ apply obs i

ddOf kns@(KnSZs0 allprops lawzdd obs) (Kw i form) =
  disSet [ forallSetQ otherps allprops (imp lawzdd (ddOf kns f)) | f <- [form, Neg form] ] where
    otherps = map (\(P n) -> n) $ allprops \\ apply obs i

ddOf kns@(KnSZs0 allprops lawzdd obs) (Ck ags form) = gfpZ lambda where
  lambda z = conSet $ ddOf kns form : [ forallSetQ (otherps i) allprops (imp lawzdd z) | i <- ags ]
  otherps i = map (\(P n) -> n) $ allprops \\ apply obs i

ddOf kns@(KnSZs0 _ _ _) (Ckw ags form) = dis (ddOf kns (Ck ags form)) (ddOf kns (Ck ags (Neg form)))

ddOf kns@(KnSZs0 props _ _) (Announce ags form1 form2) =
  imp (ddOf kns form1) (restrictQ zdd2 props (k,True)) where
    zdd2  = ddOf (announce kns ags form1) form2
    (P k) = freshp props

ddOf kns@(KnSZs0 props _ _) (AnnounceW ags form1 form2) =
  ifthenelse (ddOf kns form1) zdd2a zdd2b where
    zdd2a = restrictQs0 (ddOf (announce kns ags form1) form2) props (k,True)
    zdd2b = restrictQs0 (ddOf (announce kns ags form1) form2) props (k,False)
    (P k) = freshp props

ddOf kns@(KnSZs0 _ _ _) (PubAnnounce form1 form2) = imp (ddOf kns form1) newform2 where
    newform2 = ddOf (pubAnnounce kns form1) form2

ddOf kns@(KnSZs0 _ _ _) (PubAnnounceW form1 form2) =
  ifthenelse (ddOf kns form1) newform2a newform2b where
    newform2a = ddOf (pubAnnounce kns form1) form2
    newform2b = ddOf (pubAnnounce kns (Neg form1)) form2


--ZDD in f0s1 form

ddOf (KnSZf0 _ _ _)   Top           = botZ 
ddOf (KnSZf0 _ _ _)   Bot           = topZ 
ddOf (KnSZf0 _ _ _)   (PrpF (P n))  = varZ n 
ddOf kns@(KnSZf0 _ _ _) (Neg form) = neg (ddOf kns form)

ddOf kns@(KnSZf0 _ _ _) (Conj forms)  = disSet $ map (ddOf kns) forms
ddOf kns@(KnSZf0 _ _ _) (Disj forms)  = conSet $ map (ddOf kns) forms
ddOf kns@(KnSZf0 _ _ _) (Xor  forms)  = error "dual of xor not implemented yet"

ddOf kns@(KnSZf0 _ _ _) (Impl f g)    = impf0 (ddOf kns f) (ddOf kns g)
ddOf kns@(KnSZf0 _ _ _) (Equi f g)    = equf0 (ddOf kns f) (ddOf kns g)

ddOf kns@(KnSZf0 context _ _) (Forall ps f) = existsSetQ (map fromEnum ps) context (ddOf kns f)
ddOf kns@(KnSZf0 context _ _) (Exists ps f) = forallSetQ (map fromEnum ps) context (ddOf kns f)

ddOf kns@(KnSZf0 allprops lawzdd obs) (K i form) =
  existsSetQ otherps allprops (impf0 lawzdd (ddOf kns form)) where 
    otherps = map (\(P n) -> n) $ allprops \\ apply obs i 

ddOf kns@(KnSZf0 allprops lawzdd obs) (Kw i form) =
  conSet [ existsSetQ otherps allprops (impf0 lawzdd (ddOf kns f)) | f <- [form, Neg form] ] where
    otherps = map (\(P n) -> n) $ allprops \\ apply obs i

ddOf kns@(KnSZf0 allprops lawzdd obs) (Ck ags form) = gfpZf0 lambda where
  lambda z = disSet $ ddOf kns form : [ existsSetQ (otherps i) allprops (impf0 lawzdd z) | i <- ags ]
  otherps i = map (\(P n) -> n) $ allprops \\ apply obs i

ddOf kns@(KnSZf0 _ _ _) (Ckw ags form) = con (ddOf kns (Ck ags form)) (ddOf kns (Ck ags (Neg form)))

ddOf kns@(KnSZf0 props _ _) (Announce ags form1 form2) =
  impf0 (ddOf kns form1) (restrictQ zdd2 props (k,True)) where
    zdd2  = ddOf (announce kns ags form1) form2
    (P k) = freshp props

ddOf kns@(KnSZf0 props _ _) (AnnounceW ags form1 form2) =
  ifthenelse (ddOf kns form1) zdd2b zdd2a where
    zdd2a = restrictQ (ddOf (announce kns ags form1) form2) props (k,True)
    zdd2b = restrictQ (ddOf (announce kns ags form1) form2) props (k,False)
    (P k) = freshp props

ddOf kns@(KnSZf0 _ _ _) (PubAnnounce form1 form2) = impf0 (ddOf kns form1) newform2 where
    newform2 = ddOf (pubAnnounce kns form1) form2

ddOf kns@(KnSZf0 _ _ _) (PubAnnounceW form1 form2) =
  ifthenelse (ddOf kns form1) newform2b newform2a where
    newform2a = ddOf (pubAnnounce kns form1) form2
    newform2b = ddOf (pubAnnounce kns (Neg form1)) form2

--ZDD in f0s0 form

ddOf (KnSZf0s0 _ _ _)   Top           = botZ  
ddOf (KnSZf0s0 _ _ _)   Bot           = topZ  
ddOf (KnSZf0s0 _ _ _)   (PrpF (P n))  = neg (varZ n)
ddOf (KnSZf0s0 _ _ _)   (Neg (PrpF (P n)))    = varZ n
ddOf kns@(KnSZf0s0 _ _ _) (Neg form) = neg (ddOf kns form)

ddOf kns@(KnSZf0s0 _ _ _) (Conj forms)  = disSet $ map (ddOf kns) forms
ddOf kns@(KnSZf0s0 _ _ _) (Disj forms)  = conSet $ map (ddOf kns) forms
ddOf kns@(KnSZf0s0 _ _ _) (Xor  forms)  = xorSet $ map (ddOf kns) forms --euh improve this one

ddOf kns@(KnSZf0s0 _ _ _) (Impl f g)    = impf0 (ddOf kns f) (ddOf kns g) 
ddOf kns@(KnSZf0s0 _ _ _) (Equi f g)    = equ (ddOf kns f) (ddOf kns g)

ddOf kns@(KnSZf0s0 c _ _) (Forall ps f) = existsSetQ (map fromEnum ps) c (ddOf kns f) --ofcourse also these
ddOf kns@(KnSZf0s0 c _ _) (Exists ps f) = forallSetQ (map fromEnum ps) c (ddOf kns f)

ddOf kns@(KnSZf0s0  allprops lawzdd obs) (K i form) =
  existsSetQ otherps allprops (impf0 lawzdd (ddOf kns form)) where
    otherps = map (\(P n) -> n) $ allprops \\ apply obs i

ddOf kns@(KnSZf0s0  allprops lawzdd obs) (Kw i form) =
  conSet [ existsSetQ otherps allprops (impf0 lawzdd (ddOf kns f)) | f <- [form, Neg form] ] where
    otherps = map (\(P n) -> n) $ allprops \\ apply obs i

ddOf kns@(KnSZf0s0  allprops lawzdd obs) (Ck ags form) = gfpZf0 lambda where
  lambda z = disSet $ ddOf kns form : [ existsSetQ (otherps i) allprops (impf0 lawzdd z) | i <- ags ]
  otherps i = map (\(P n) -> n) $ allprops \\ apply obs i

ddOf kns@(KnSZf0s0  _ _ _) (Ckw ags form) = con (ddOf kns (Ck ags form)) (ddOf kns (Ck ags (Neg form)))

ddOf kns@(KnSZf0s0  props _ _) (Announce ags form1 form2) =
  impf0 (ddOf kns form1) (restrictQ zdd2 props (k,True)) where
    zdd2  = ddOf (announce kns ags form1) form2
    (P k) = freshp props

ddOf kns@(KnSZf0s0  props _ _) (AnnounceW ags form1 form2) =
  ifthenelse (ddOf kns form1) zdd2b zdd2a where
    zdd2a = restrictQs0 (ddOf (announce kns ags form1) form2) props (k,True)
    zdd2b = restrictQs0 (ddOf (announce kns ags form1) form2) props (k,False)
    (P k) = freshp props

ddOf kns@(KnSZf0s0  _ _ _) (PubAnnounce form1 form2) = impf0 (ddOf kns form1) newform2 where
    newform2 = ddOf (pubAnnounce kns form1) form2

ddOf kns@(KnSZf0s0  _ _ _) (PubAnnounceW form1 form2) =
  ifthenelse (ddOf kns form1) newform2b newform2a where
    newform2a = ddOf (pubAnnounce kns form1) form2
    newform2b = ddOf (pubAnnounce kns (Neg form1)) form2

ddOf _ (Dia _ _) = error "Dynamic operators are not implemented for CUDD."
ddOf _ _ = error "zddOf with a wrong kns type"

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
  ,as, ": \\\\ \\[", giveZddTex a, "\\] \\\\ \n"
  ,bs, ": \\\\ \\[", giveZddTex b, "\\] \\\\ \n"
  ,cs, ": \\\\ \\[", giveZddTex c, "\\] \\\\ \n"
  ,a2s, ": \\\\ \\[", giveZddTex a2, "\\] \\\\ \n"
  ,b2s, ": \\\\ \\[", giveZddTex b2, "\\] \\\\ \n"
  ,c2s, ": \\\\ \\[", giveZddTex c2, "\\] \\\\ \n"
  --,ds, ": \\\\ \\[", giveZddTex d, "\\] \\\\ \n"
  --,d2s, ": \\\\ \\[", giveZddTex d2, "\\] \\\\ \n"
  --,es, ": \\\\ \\[", giveZddTex e, "\\] \\\\ \n"
  --,e2s, ": \\\\ \\[", giveZddTex e2, "\\] \\\\ \n"
  --,e3s, ": \\\\ \\[", giveZddTex e3, "\\] \\\\ \n"
  --,fs, ": \\\\ \\[", giveZddTex f, "\\] \\\\ \n"
  --,gs, ": \\\\ \\[", giveZddTex g, "\\] \\\\ \n"
  --,hs, ": \\\\ \\[", giveZddTex h, "\\] \\\\ \n"
  --,is, ": \\\\ \\[", giveZddTex i, "\\] \\\\ \n"
  --,js, ": \\\\ \\[", giveZddTex j, "\\] \\\\ \n"
  --,ks, ": \\\\ \\[", giveZddTex k, "\\] \\\\ \n"
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

    --is = "ZDD: var 1"
    --i = varZ 1
    --js = "ZDD: only var 1"
    --j = neg $ varZ 1

    as = "ZDD: (2 con neg 1) imp (neg 3)"
    a = (varZ 2 `con` (neg $ varZ 1)) `imp` (neg $ varZ 3)
    bs = "ZDD Conversion: Forall 1 ((2 con neg 1) imp (neg 3))"
    b = createZddFromBdd (forall 1 ((var 2 `con` (neg $ var 1)) `imp` (neg $ var 3)))
    cs = "ZDD: Forall 1 ((2 con neg 1) imp (neg 3))"
    c = forallQ 1 (map P [1,2,3]) ((varZ 2 `con` (neg $ varZ 1)) `imp` (neg $ varZ 3))

    a2s = "ZDD: (neg 1 imp ( neg 3)) con (2 imp (neg 3))"
    a2 = ((neg $ varZ 1) `imp` ( neg $ varZ 3)) `con` (varZ 2 `imp` ((neg $ varZ 3 ) `dis` varZ 1))
    b2s = "ZDD Conversion: (exists 1 ((neg 1 imp ( neg 3) con 2 imp (neg 3)))"
    b2 = createZddFromBdd (exists 1 (((neg $ var 1) `imp` ( neg $ var 3)) `con` (var 2 `imp` ((neg $ var 3 ) `dis` var 1))))
    c2s = "ZDD: (exists 1 ((neg 1 imp ( neg 3) con 2 imp (neg 3)))"
    c2 = existsQ 1 (map P [1,2,3]) (((neg $ varZ 1) `imp` ( neg $ varZ 3)) `con` (varZ 2 `imp` ((neg $ varZ 3 ) `dis` varZ 1)))

    --ds = "ZDD: sub0 ((neg 1 imp ( neg 3)) con 2 imp (neg 3))"
    --d = sub0 ((neg $ varZ 1 `imp` ( neg $ varZ 3)) `con` (varZ 2 `imp` (neg $ varZ 3 ))) 1 
    --d2s = "ZDD: sub1 ((neg 1 imp ( neg 3)) con 2 imp (neg 3))"
    --d2 = sub1 (((neg $ varZ 1) `imp` ( neg $ varZ 3)) `con` (varZ 2 `imp` (neg $ varZ 3 ))) 1 
    --e3s = "ZDD: product 1 (sub1 ((neg 1 imp ( neg 3)) con 2 imp (neg 3) imp Top)"
    --e3 = productZ (sub1 (((neg $ varZ 1) `imp` ( neg $ varZ 3)) `con` (varZ 2 `imp` (neg $ varZ 3 ))) 1 )  (exceptVarZContext (map P [1,2,3]) 1)
    --e2s = "ZDD: product 1 (sub0 ((neg 1 imp ( neg 3)) con 2 imp (neg 3) imp Bot)"
    --e2 = productZ (sub0 (((neg $ varZ 1) `imp` ( neg $ varZ 3)) `con` (varZ 2 `imp` (neg $ varZ 3 ))) 1 ) (exceptVarZContext (map P [1,2,3]) 1)
    

    --fs = "ZDD: (neg 1 imp ( neg 3)) con 2 imp (neg 3)"
    --f = (((neg $ varZ 1) `imp` ( neg $ varZ 3)) `con` (varZ 2 `imp` (neg $ varZ 3 )))
    --gs = "ZDD Conv: (neg 1 imp ( neg 3)) con 2 imp (neg 3)"
    --g = createZddFromBdd (((neg $ var 1) `imp` ( neg $ var 3)) `con` (var 2 `imp` (neg $ var 3 )))

    --zs = "ZDD: neg 2 con neg 3 "
    --z = (neg $ varZ 2) `con` (neg $ varZ 3)
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







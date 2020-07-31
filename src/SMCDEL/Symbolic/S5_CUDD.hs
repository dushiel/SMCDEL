{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

module SMCDEL.Symbolic.S5_CUDD where

import SMCDEL.Internal.MyHaskCUDD
import Data.List ((\\))
import SMCDEL.Internal.Help (apply)
import SMCDEL.Language
import System.IO.Unsafe

boolBddOf :: Form -> Bdd
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

data KnowStruct = KnS [Prp] Bdd [(Agent,[Prp])] | KnSZ [Prp] Zdd [(Agent,[Prp])] deriving (Eq,Show)
type KnState = [Prp]
type KnowScene = (KnowStruct,KnState)

instance HasVocab KnowStruct where
  vocabOf (KnS props _ _) = props

instance Pointed KnowStruct KnState

pubAnnounce :: KnowStruct -> Form -> KnowStruct
pubAnnounce kns@(KnS props lawbdd obs) psi = KnS props newlawbdd obs where
  newlawbdd = con lawbdd (bddOf kns psi)

announce :: KnowStruct -> [Agent] -> Form -> KnowStruct
announce kns@(KnS props lawbdd obs) ags psi = KnS newprops newlawbdd newobs where
  proppsi@(P k) = freshp props
  newprops  = proppsi:props
  newlawbdd = con lawbdd (equ (var k) (bddOf kns psi))
  newobs    = [(i, apply obs i ++ [proppsi | i `elem` ags]) | i <- map fst obs]

bddOf :: KnowStruct -> Form -> Bdd
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
    otherps = map (\(P n) -> n) $ allprops \\ apply obs i
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

evalViaBdd :: KnowScene -> Form -> Bool 
evalViaBdd (kns@(KnS allprops _ _),s) f = bool where
  bool | b==top = True
       | b==bot = False
       | otherwise = error ("evalViaBdd failed: BDD leftover:\n" ++ show b)
  b    = restrictSet (bddOf kns f) list
  list = [ (n, P n `elem` s) | (P n) <- allprops ]

instance Semantics KnowScene where
  isTrue = evalViaBdd

validViaBdd :: KnowStruct -> Form -> Bool
validViaBdd kns@(KnS _ lawbdd _) f = top == lawbdd `imp` bddOf kns f

-- ZDD stuff (also see data type declarations above)

zddOf :: KnowStruct -> Form -> Zdd
zddOf _   Top           = topZ
zddOf _   Bot           = botZ
zddOf _   (PrpF (P n))  = varZ n
zddOf kns (Neg form)    = negZ $ zddOf kns form

{-zddOf kns (Conj forms)  = conSet $ map (zddOf kns) forms
zddOf kns (Disj forms)  = disSet $ map (zddOf kns) forms
zddOf kns (Xor  forms)  = xorSet $ map (zddOf kns) forms

zddOf kns (Impl f g)    = imp (zddOf kns f) (zddOf kns g)
zddOf kns (Equi f g)    = equ (zddOf kns f) (zddOf kns g)

zddOf kns (Forall ps f) = forallSet (map fromEnum ps) (zddOf kns f)
zddOf kns (Exists ps f) = existsSet (map fromEnum ps) (zddOf kns f)

zddOf kns@(KnS allprops lawzdd obs) (K i form) =
  forallSet otherps (imp lawzdd (zddOf kns form)) where
    otherps = map (\(P n) -> n) $ allprops \\ apply obs i
zddOf kns@(KnS allprops lawzdd obs) (Kw i form) =
  disSet [ forallSet otherps (imp lawzdd (zddOf kns f)) | f <- [form, Neg form] ] where
    otherps = map (\(P n) -> n) $ allprops \\ apply obs i
zddOf kns@(KnS allprops lawzdd obs) (Ck ags form) = gfp lambda where
  lambda z = conSet $ zddOf kns form : [ forallSet (otherps i) (imp lawzdd z) | i <- ags ]
  otherps i = map (\(P n) -> n) $ allprops \\ apply obs i
zddOf kns (Ckw ags form) = dis (zddOf kns (Ck ags form)) (zddOf kns (Ck ags (Neg form)))
zddOf kns@(KnS props _ _) (Announce ags form1 form2) =
  imp (zddOf kns form1) (restrict zdd2 (k,True)) where
    zdd2  = zddOf (announce kns ags form1) form2
    (P k) = freshp props
zddOf kns@(KnS props _ _) (AnnounceW ags form1 form2) =
  ifthenelse (zddOf kns form1) zdd2a zdd2b where
    zdd2a = restrict (zddOf (announce kns ags form1) form2) (k,True)
    zdd2b = restrict (zddOf (announce kns ags form1) form2) (k,False)
    (P k) = freshp props
zddOf kns (PubAnnounce form1 form2) = imp (zddOf kns form1) newform2 where
    newform2 = zddOf (pubAnnounce kns form1) form2
zddOf kns (PubAnnounceW form1 form2) =
  ifthenelse (zddOf kns form1) newform2a newform2b where
    newform2a = zddOf (pubAnnounce kns form1) form2
    newform2b = zddOf (pubAnnounce kns (Neg form1)) form2-}

zddOf _ (Dia _ _) = error "Dynamic operators are not implemented for CUDD."



validViaZddTest :: KnowStruct -> Form -> Bool

{-validViaZddTest kns@(KnS _ lawbdd _)  f = topZ == lawzdd 'differenceZ' transformedZdd where 
-  transformedZdd = createZddFromBdd (bddOf kns f)
  lawzdd = createZddFromBdd lawbdd

 currently the printfunction needs to be called for the variables to be evaluated correctly, 
 ask Malvin if he knows why. 
-}

validViaZddTest kns@(KnS _ lawbdd _)  f = unsafePerformIO $ do
  let transformedZdd = createZddFromBdd $ bddOf kns f
  let lawzdd = createZddFromBdd $ lawbdd
  let b = differenceZ lawzdd transformedZdd
  putStrLn "... forceprint of b and z to compare"
  printZddInfo b
  let z = botZ
  printZddInfo z
  let r = z == b
  if r then putStrLn ("comparison: True \n") else putStrLn (".. comparison: False \n")
  dotPrintZ transformedZdd
  return r

evalViaZdd :: KnowScene -> Form -> Bool
evalViaZdd (kns@(KnSZ allprops _ obs),s) f = bool where
  bool = validViaZddTest newKnSZ f
  newKnSZ = KnSZ allprops restrictedZdd obs
  restrictedZdd = restrictSetZ (createZddFromBdd (bddOf kns f)) list
  list = [ (n, P n `elem` s) | (P n) <- allprops ]

--dot print

dotPrintZ :: Zdd -> IO()
dotPrintZ b = writeZdd b "hello_zdd_graph"

dotPrint :: Bdd -> IO()
dotPrint b = writeBdd b "hello_bdd_graph"
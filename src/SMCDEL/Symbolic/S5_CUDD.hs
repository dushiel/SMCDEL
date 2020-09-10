{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

module SMCDEL.Symbolic.S5_CUDD where

import SMCDEL.Internal.MyHaskCUDD
import Data.List ((\\))
import SMCDEL.Internal.Help (apply)
import SMCDEL.Language
import System.IO.Unsafe
import Debug.Trace

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

data KnowStruct = KnS [Prp] !Bdd [(Agent,[Prp])] | KnSZ [Prp] !Zdd [(Agent,[Prp])] deriving (Eq,Show)
type KnState = [Prp]
type KnowScene = (KnowStruct,KnState)

instance HasVocab KnowStruct where
  vocabOf (KnS props _ _) = props

instance Pointed KnowStruct KnState

pubAnnounce :: KnowStruct -> Form -> KnowStruct
pubAnnounce kns@(KnS props lawbdd obs) psi = KnS props newlawbdd obs where
  newlawbdd = con lawbdd (bddOf kns psi)
pubAnnounce kns@(KnSZ props lawzdd obs) psi = KnSZ props newlawzdd obs where
  newlawzdd = conZ lawzdd (zddOf kns psi)

announce :: KnowStruct -> [Agent] -> Form -> KnowStruct
announce kns@(KnS props lawbdd obs) ags psi = KnS newprops newlawbdd newobs where
  proppsi@(P k) = freshp props
  newprops  = proppsi:props
  newlawbdd = con lawbdd (equ (var k) (bddOf kns psi))
  newobs    = [(i, apply obs i ++ [proppsi | i `elem` ags]) | i <- map fst obs]
announce kns@(KnSZ props lawzdd obs) ags psi = KnSZ newprops newlawzdd newobs where
  proppsi@(P k) = freshp props
  newprops  = proppsi:props
  newlawzdd = conZ lawzdd (equZ (varZ k) (zddOf kns psi))
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

boolZddOf :: Form -> Zdd
boolZddOf Top           = topZ
boolZddOf Bot           = botZ
boolZddOf (PrpF (P n))  = varZ n
boolZddOf (Neg form)    = negZ (boolZddOf form)
boolZddOf (Conj forms)  = conSetZ $ map boolZddOf forms
boolZddOf (Disj forms)  = disSetZ $ map boolZddOf forms
boolZddOf (Impl f g)    = impZ (boolZddOf f) (boolZddOf g)
boolZddOf (Equi f g)    = equZ (boolZddOf f) (boolZddOf g)
boolZddOf (Forall ps f) = boolZddOf (foldl singleForall f ps) where
  singleForall g p = Conj [ substit p Top g, substit p Bot g ]
boolZddOf (Exists ps f) = boolZddOf (foldl singleExists f ps) where
  singleExists g p = Disj [ substit p Top g, substit p Bot g ]
boolZddOf _             = error "boolZddOf failed: Not a boolean formula."

zddOf :: KnowStruct -> Form -> Zdd
zddOf _   Top           = topZ
zddOf _   Bot           = botZ
zddOf _   (PrpF (P n))  = varZ n
zddOf kns (Neg form) = negZ (zddOf kns form)

zddOf kns (Conj forms)  = conSetZ $ map (zddOf kns) forms
zddOf kns (Disj forms)  = disSetZ $ map (zddOf kns) forms
zddOf kns (Xor  forms)  = xorSetZ $ map (zddOf kns) forms

zddOf kns (Impl f g)    = impZ (zddOf kns f) (zddOf kns g)
zddOf kns (Equi f g)    = equZ (zddOf kns f) (zddOf kns g)

zddOf kns (Forall ps f) = forallSetZ (map fromEnum ps) (zddOf kns f)
zddOf kns (Exists ps f) = existsSetZ (map fromEnum ps) (zddOf kns f)

zddOf kns@(KnSZ allprops lawzdd obs) (K i form) =
  forallSetZ otherps (impZ lawzdd (zddOf kns form)) where
    otherps = map (\(P n) -> n) $ allprops \\ apply obs i

zddOf kns@(KnSZ allprops lawzdd obs) (Kw i form) =
  disSetZ [ forallSetZ otherps (impZ lawzdd (zddOf kns f)) | f <- [form, Neg form] ] where
    otherps = map (\(P n) -> n) $ allprops \\ apply obs i

zddOf kns@(KnSZ allprops lawzdd obs) (Ck ags form) = gfpZ lambda where
  lambda z = conSetZ $ zddOf kns form : [ forallSetZ (otherps i) (impZ lawzdd z) | i <- ags ]
  otherps i = map (\(P n) -> n) $ allprops \\ apply obs i

zddOf kns (Ckw ags form) = disZ (zddOf kns (Ck ags form)) (zddOf kns (Ck ags (Neg form)))

zddOf kns@(KnSZ props _ _) (Announce ags form1 form2) =
  impZ (zddOf kns form1) (restrictZ zdd2 (k,True)) where
    zdd2  = zddOf (announce kns ags form1) form2
    (P k) = freshp props

zddOf kns@(KnSZ props _ _) (AnnounceW ags form1 form2) =
  ifthenelseZ (zddOf kns form1) zdd2a zdd2b where
    zdd2a = restrictZ (zddOf (announce kns ags form1) form2) (k,True)
    zdd2b = restrictZ (zddOf (announce kns ags form1) form2) (k,False)
    (P k) = freshp props

zddOf kns (PubAnnounce form1 form2) = impZ (zddOf kns form1) newform2 where
    newform2 = zddOf (pubAnnounce kns form1) form2

zddOf kns (PubAnnounceW form1 form2) =
  ifthenelseZ (zddOf kns form1) newform2a newform2b where
    newform2a = zddOf (pubAnnounce kns form1) form2
    newform2b = zddOf (pubAnnounce kns (Neg form1)) form2

zddOf _ (Dia _ _) = error "Dynamic operators are not implemented for CUDD."

validViaZdd :: KnowStruct -> Form -> Bool
validViaZdd kns@(KnSZ _ lawzdd _) f = unsafePerformIO $! do 
  let a = (exists 2 (var 3)) `imp` var 3
  let b = (existsZ 2 (varZ 3)) `impZ` varZ 3
  let c = (varZ 1 `conZ` botZ) `impZ` (varZ 1 `disZ` topZ)

  let x = neg (forall 2 (neg $ var 3)) `imp` (var 3)
  let y = negZ (forallZ 2 (negZ $ varZ 3)) `impZ` (varZ 3)

  --putStrLn ("basic check, 1&bot -> 1|top: " ++ show (c == topZ))
  --printZddInfo c "basic check"
  putStrLn ("exists zdd equal to bdd: " ++ show ((a == top) == (b == topZ)))
  putStrLn ("forall zdd equal to bdd: " ++ show ((x == top) == (y == topZ)))
  --putStrLn ("bdd exists and forall the same: " ++ show (a == x) ++ ", zdd exists and forall:" ++ show(b == y))
  --printZddInfo ((negZ $ varZ 3) `impZ` (varZ 1)) "~3 ->1"--`impZ` varZ 1) "~3 -> 1"
   
  let z = topZ == lawzdd `impZ` (zddOf kns f) 
  return z

convertTest :: KnowStruct -> Form -> Bool
convertTest kns@(KnS _ law _) query = unsafePerformIO $ do
  let q = createZddFromBdd (bddOf kns query)
  let l = createZddFromBdd law
  let r = l `impZ` q
  printZddInfo q "convertionn result"
  return (r == topZ)

evalViaZdd :: KnowScene -> Form -> Bool
evalViaZdd (kns@(KnSZ allprops _ obs),s) f = bool where
  bool | z==topZ = True
       | z==botZ = False
       | otherwise = error ("evalViaZdd failed: ZDD leftover:\n" ++ show z)
  z    = restrictSetZ (zddOf kns f) list
  list = [ (n, P n `elem` s) | (P n) <- allprops ]


initZddVars :: [Int] -> IO()
initZddVars vocab = do
  let v = initZddVarsWithInt vocab
  printZddInfo v "init!"
  --portVars
  return ()

prpToInt :: [Prp] -> [Int]
prpToInt vocab = map (\(P n) -> n) vocab

--dot print

dotPrintZ :: Zdd -> IO()
dotPrintZ b = writeZdd b "hello_zdd_graph"

dotPrint :: Bdd -> IO()
dotPrint b = writeBdd b "hello_bdd_graph"
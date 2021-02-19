{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

module SMCDEL.Symbolic.S5_CUDD where

import SMCDEL.Internal.MyHaskCUDD
import Data.List ((\\))
import SMCDEL.Internal.Help (apply)
import SMCDEL.Language
import System.IO.Unsafe
import Data.List ((\\),delete,dropWhile,dropWhileEnd,intercalate,intersect,nub,sort)
--import Data.Tagged
import SMCDEL.Internal.TexDisplay
import System.Process (runInteractiveCommand)
import System.IO (hPutStr, hGetContents, hClose)
import Data.Char (isSpace)
--------------------------
import Data.GraphViz  
--import Text.RE.Tools.Grep
import qualified Data.Text.Lazy as B
import qualified Data.Text.Lazy.IO as L
import qualified Data.GraphViz.Types.Generalised as GraphGen
import qualified Data.GraphViz.Algorithms as GraphAlg
import Data.GraphViz.Printing (renderDot)
import qualified Data.GraphViz.Attributes.Complete as GraphAttr

---------------------------
import Control.DeepSeq (rnf)
import Data.Typeable
import Data.Text.Lazy (pack)

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

data KnowStruct = KnS [Prp] !(Dd B) [(Agent,[Prp])] | KnSZ [Prp] !(Dd Z) [(Agent,[Prp])] deriving (Eq,Show)
type KnState = [Prp] 
type KnowScene = (KnowStruct,KnState)

instance HasVocab KnowStruct where
  vocabOf (KnS props _ _) = props

instance Pointed KnowStruct KnState

pubAnnounce :: KnowStruct -> Form -> KnowStruct
pubAnnounce kns@(KnS props lawbdd obs) psi = KnS props newlawbdd obs where
  newlawbdd = con lawbdd (bddOf kns psi)
pubAnnounce kns@(KnSZ props lawzdd obs) psi = KnSZ props newlawzdd obs where
  newlawzdd = con lawzdd (zddOf kns psi)

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


convertTest :: KnowStruct -> Form -> Bool
convertTest kns@(KnS _ law _) query = unsafePerformIO $ do
  let q = createZddFromBdd (bddOf kns query)
  let l = createZddFromBdd law
  let r = l `imp` q
  --printZddInfo q "convertionn result"
  return (r == topZ)

initZddVars :: [Int] -> IO()
initZddVars vocab = do
  let v = initZddVarsWithInt vocab
  _ <- return $! rnf (forceCheckDd v)
  return ()

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

--------------querying

validViaZdd :: KnowStruct -> Form -> Bool
validViaZdd kns@(KnSZ _ lawzdd _) f = topZ == lawzdd `imp` zddOf kns f

evalViaZdd :: KnowScene -> Form -> Bool
evalViaZdd (kns@(KnSZ allprops _ obs),s) f = bool where
  bool | z==topZ = True
       | z==botZ = False
       | otherwise = error ("evalViaZdd failed: ZDD leftover:\n" ++ show z)
  z    = restrictSet (zddOf kns f) list
  list = [ (n, P n `elem` s) | (P n) <- allprops ]


--------------Debugging!

{-
mudScnInit :: Int -> Int -> KnowScene
mudScnInit n m = (KnS vocab law obs, actual) where
  vocab  = [P 1 .. P n]
  law    = boolBddOf Top
  obs    = [ (show i, delete (P i) vocab) | i <- [1..n] ]
  actual = [P 1 .. P m]
-}

giveDebugTex :: String
giveDebugTex = concat [
  "Testing evalviaZdd (restrict set), see S5\\_CUDD.giveBasicZddTex for implementation.\\\\ \n"
  ,as, ": \\\\ \\[", giveZddTex a, "\\] \\\\ \n"
  ,bs, ": \\\\ \\[", giveZddTex b, "\\] \\\\ \n"
  ,cs, ": \\\\ \\[", giveZddTex c, "\\] \\\\ \n"
  ,ds, ": \\\\ \\[", giveZddTex d, "\\] \\\\ \n"
  ,es, ": \\\\ \\[", giveZddTex e, "\\] \\\\ \n"
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
    as = "neg 1 con neg 3"
    a = neg ( varZ 1) `con` neg ( varZ 3)
    bs = "neg 1 con neg 3, s = neg 1"
    b = restrictSet (neg ( varZ 1) `con` neg ( varZ 3)) [(1, False)]
    cs = "neg 1 con neg 3, s = 2"
    c = restrictSet (neg ( varZ 1) `con` neg ( varZ 3)) [(2, True)]
    ds = "sub0 (neg 1 con neg 3) 1"
    d = sub0 (neg ( varZ 1) `con` neg ( varZ 3)) 1
    es = "sub1 (neg 1 con neg 3) 1"
    e = sub1 (neg ( varZ 1) `con` neg ( varZ 3)) 1


comparisonTestZddVsBdd :: String
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
    e = neg (varZ 4 `con` (varZ 3 `con` (varZ 2 `con` (varZ 1))))


    
--------------------------- Texable functionality

{-texDdBwith :: (Int -> String) -> Dd B -> String --it decides what the variable names are
texDdBwith myShow d = unsafePerformIO $ do
  (i,o,_,_) <- runInteractiveCommand "dot2tex --figpreamble=\"\\huge\" --figonly -traw"
  hPutStr i (returnDot d ++ "\n")
  hClose i

  --very ugly method for getting the correct type, find out a method for knowing the type of retur
  writeToDot d "tempBdd.dot"
  xDotText <- L.readFile "tempBdd.dot"

  let xDotGraph = parseDotGraphLiberally xDotText :: GraphGen.DotGraph String
  let updatedXDotGraph = changeMyGraph myShow (GraphAlg.canonicalise xDotGraph)
  --L.putStrLn $ renderDot $ toDot xDotGraph
  print $ graphNodes updatedXDotGraph
  --print $ graphEdges xDotGraph

  result <- hGetContents o
  return $ dropWhileEnd isSpace $ dropWhile isSpace result-}

texDdB :: Dd B -> String 
texDdB d = unsafePerformIO $ do
  (i,o,_,_) <- runInteractiveCommand "dot2tex --figpreamble=\"\\huge\" --figonly -traw"

  -- replace with B.pack returnDot d, with a clean method for de-IO-ing returnDot (use hGetContents?)
  writeToDot d "tempBdd.dot"
  xDotText <- L.readFile "tempBdd.dot"

  -- let xDotGraph = parseDotGraphLiberally xDotText :: GraphGen.DotGraph String
  --let clusteredXDotGraph = clusterMyGraph xDotGraph
  --let updatedXDotGraph = changeMyGraph GraphAlg.canonicalise clusteredXDotGraph
  --L.putStrLn $ renderDot $ toDot xDotGraph 
  --print $ graphNodes updatedXDotGraph
  -- print updatedXDotGraph

  --hPutStr i (B.unpack (renderDot $ toDot updatedXDotGraph) ++ "\n")
  hPutStr i (returnDot d ++ "\n")
  hClose i
  result <- hGetContents o
  return $ dropWhileEnd isSpace $ dropWhile isSpace result

texDdZ :: Dd Z -> String
texDdZ d = unsafePerformIO $ do
  (i,o,_,_) <- runInteractiveCommand "dot2tex --figpreamble=\"\\huge\" --figonly -traw"
  hPutStr i (returnDot d ++ "\n")
  hClose i
  result <- hGetContents o
  return $ dropWhileEnd isSpace $ dropWhile isSpace result

--texBDD :: Bdd -> String
--texBDD = texBddWith show

--newtype WrapBdd = Wrap Bdd

--instance TexAble WrapBdd where
--  tex (Wrap b) = texBDD b

instance TexAble KnowStruct where
  tex (KnS props lawbdd obs) = concat
    [ " \\left( \n"
    , tex props ++ ", "
    , " \\begin{array}{l} \\scalebox{0.4}{"
    , texDdB lawbdd
    , "} \\end{array}\n "
    , ", \\begin{array}{l}\n"
    , intercalate " \\\\\n " (map (\(_,os) -> tex os) obs)
    , "\\end{array}\n"
    , " \\right)" ]
  tex (KnSZ props lawzdd obs) = concat
    [ " \\left( \n"
    , tex props ++ ", "
    , " \\begin{array}{l} \\scalebox{0.4}{"
    , texDdZ lawzdd
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

portvar :: IO()
portvar = portVars

changeMyGraph :: DotGraph String -> DotGraph String
changeMyGraph dg =
  dg { graphStatements = (graphStatements dg) { nodeStmts = map changeDotNode (nodeStmts (graphStatements dg)) } } where
  changeDotNode dn = dn { nodeAttributes = map changeNodeAttributes (nodeAttributes dn) }
  changeNodeAttributes na = case na of
    -- i am not sold on my usage of the read function here, i do not check whether the string is actually convertable to string and i feel like Text.Lazy has a read function of its own
    --GraphAttr.Label (GraphAttr.StrLabel s) -> GraphAttr.Label (GraphAttr.StrLabel (B.pack (myShow (read (B.unpack s) :: Int))))
    GraphAttr.Label (GraphAttr.StrLabel s) -> GraphAttr.Label (GraphAttr.StrLabel (B.pack $ show ((read (B.unpack s) :: Int) + 1 )))
    x                  -> x

{-clusterMyGraph :: DotGraph String -> DotGraph String
clusterMyGraph dg =
  dg { graphStatements = (graphStatements dg) { nodeStmts = map changeDotNode (nodeStmts (graphStatements dg)) } } where
  changeDotNode dn = dn { nodeAttributes = map changeNodeAttributes (nodeAttributes dn) }
  changeNodeAttributes na = case na of
    -- i am not sold on my usage of the read function here, i do not check whether the string is actually convertable to string and i feel like Text.Lazy has a read function of its own
    --GraphAttr.Label (GraphAttr.StrLabel s) -> GraphAttr.Label (GraphAttr.StrLabel (B.pack (myShow (read (B.unpack s) :: Int))))
    GraphAttr.Label (GraphAttr.StrLabel s) -> GraphAttr.Label (GraphAttr.StrLabel (B.pack $ show ((read (B.unpack s) :: Int) + 1 )))
    x                  -> x
-}

{- subgraph version
changeMyGraph :: DotGraph String -> DotGraph String
changeMyGraph dg =
  dg { graphStatements = (graphStatements dg) { subGraphs = map changeDotNode (subGraphs (graphStatements dg)) } } where
  changeDotSubGraph dn = dn { nodeAttribbutes = map changeSubGraphAttributes (nodeAttributes dn) }
  changeSubGraphAttributes na = case na of
    -- i am not sold on my usage of the read function here, i do not check whether the string is actually convertable to string and i feel like Text.Lazy has a read function of its own
    --GraphAttr.Label (GraphAttr.StrLabel s) -> GraphAttr.Label (GraphAttr.StrLabel (B.pack (myShow (read (B.unpack s) :: Int))))
    GraphAttr.Label (GraphAttr.StrLabel s) -> GraphAttr.Label (GraphAttr.StrLabel (B.pack $ show ((read (B.unpack s) :: Int) + 1 )))
    x                  -> x

-}



{-
load in the dot file/string given by dump dot, with: format :: String -> String


change list:
-remove strict, only digraph
-remove label from rank
-give nodes the labels
-check when and why some nodes do not have boundaries (edge = invis)
-make the dotted lines go to Bot (new node)
-remove edge [dir = none];
-probably remove size = "7.5,10", center = true;

what does x do?:
- " 2 " -> " 3 " -> "CONST NODES"; 
- strict
- the first top node, does it have a purpose?



example from correct to current:

strict digraph g {
n0 [label="2",shape="circle"];
n0 -> Top;
n0 -> n1 [style=dashed];
n1 [label="3",shape="circle"];
n1 -> Top;
n1 -> Bot [style=dashed];
Bot [label="0",shape="box"];
Top [label="1",shape="box"];
{ rank=same; n0 }
{ rank=same; n1 }
}


digraph "DD" {
size = "7.5,10"
center = true;
edge [dir = none];
{ node [shape = plaintext];
  edge [style = invis];
  "CONST NODES" [style = invis];
" 2 " -> " 3 " -> "CONST NODES"; 
}
{ rank = same; node [shape = box]; edge [style = invis];
"F0"; }
{ rank = same; " 2 ";
"0x30b";
}
{ rank = same; " 3 ";
"0x30a";
}
{ rank = same; "CONST NODES";
{ node [shape = box]; "0x2da";
}
}
"F0" -> "0x30b" [style = solid];
"0x30b" -> "0x2da";
"0x30b" -> "0x30a" [style = dashed];
"0x30a" -> "0x2da";
"0x30a" -> "0x2da" [style = dotted];
"0x2da" [label = "1"];
}


-}

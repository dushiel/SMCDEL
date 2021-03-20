module SMCDEL.Internal.MyHaskCUDD (
  -- * Types
  Dd, B, Z,
  -- * Creation of new BDDs
  top, bot, var,
  -- * Combination and Manipulation of BDDs
  neg, con, dis, imp, equ, xor, conSet, disSet, xorSet,
  exists, forall, forallSet, existsSet,
  restrict, restrictSet,
  ifthenelse, returnDot,
  gfp, existsQ, forallQ, forallSetQ, existsSetQ,
  -- * extra Zdd functionalities
  gfpZ, gfpZf0, writeToDot, printDdInfo, differenceZ, portVars, initZddVarsWithInt, topZ, varZ, botZ,
  createZddFromBdd, forceCheckDd, sub0, sub1, productZ, complementZ, exceptVarZContext, exceptVarZContext2,
  restrictQ, restrictQs0, restrictSetQ, restrictSetQs0, equf0, impf0, negf0, swaps0
) where

import qualified Cudd.Cudd
import System.IO.Unsafe ( unsafePerformIO )
import System.IO.Temp ( withSystemTempDirectory )
import Debug.Trace (trace)
import SMCDEL.Language (Prp)

{-onlyBothVarZ :: Int -> Dd Z 
onlyBothVarZ n = complementZ $ neg $ varZ n

onlyNotVarZ :: Int -> Dd Z
onlyNotVarZ n = complementZ $ varZ n-}

exceptVarZContext :: [Prp] -> Int -> Dd Z  
exceptVarZContext [n] except 
  | fromEnum n /= except   = neg $ varZ (fromEnum n) --`debug` "final"
  | fromEnum n == except   = topZ --`debug` "topZ final"
exceptVarZContext (n: ns) except 
  | fromEnum n /= except   = (neg $ varZ (fromEnum n)) `con` exceptVarZContext ns except --`debug` ("passed")
  | fromEnum n == except   = exceptVarZContext ns except --`debug` ("except " ++ show(except))
exceptVarZContext _ _ = error "empty context list for conPropsExceptVar"

exceptVarZContext2 :: [Prp] -> Int -> Dd Z  
exceptVarZContext2 _ n = differenceZ topZ (neg $ varZ n)

complementZ :: Dd Z -> Dd Z 
complementZ (ToDd z) = ToDd $ Cudd.Cudd.cuddZddComplement manager z

sub0 :: Dd Z -> Int -> Dd Z
sub0 z n = ToDd $ Cudd.Cudd.cuddZddSub0 manager zmin n where
  ToDd zmin = z
sub1 :: Dd Z -> Int -> Dd Z
sub1 (ToDd z) n = ToDd $ Cudd.Cudd.cuddZddSub1 manager z n 
swaps0 :: Dd Z -> [Int] -> Dd Z 
swaps0 (ToDd z) [n] = ToDd $ Cudd.Cudd.cuddZddChange manager z n
swaps0 (ToDd z) (n:ns) = swaps0 (ToDd $ Cudd.Cudd.cuddZddChange manager z n) ns
swaps0 z [] = z

productZ :: Dd Z -> Dd Z -> Dd Z
productZ (ToDd z1) (ToDd z2) = ToDd $ Cudd.Cudd.cuddZddProduct manager z1 z2

manager :: Cudd.Cudd.DdManager
manager = Cudd.Cudd.cuddInit

newtype Dd x = ToDd Cudd.Cudd.DdNode deriving (Eq,Show)
data B
data Z

bot :: Dd B 
bot = ToDd (Cudd.Cudd.cuddReadLogicZero manager)
top :: Dd B
top = ToDd (Cudd.Cudd.cuddReadOne manager)
var :: Int -> Dd B
var n = ToDd (Cudd.Cudd.cuddBddIthVar manager n) --`debug` ("var " ++ show n)

topZ :: Dd Z
topZ = ToDd (Cudd.Cudd.cuddZddReadOne manager)
botZ :: Dd Z
botZ = ToDd (Cudd.Cudd.cuddZddReadZero manager)
varZ :: Int -> Dd Z
varZ n = ToDd (Cudd.Cudd.cuddZddIthVar manager n) --`debug` ("varZ " ++ show n)

-------------------------------------------------------------------------------------------

class DdF a where
  neg :: Dd a -> Dd a
  negf0 :: Dd a -> Dd a
  con :: Dd a -> Dd a -> Dd a
  dis :: Dd a -> Dd a -> Dd a
  xor :: Dd a -> Dd a -> Dd a
  equ :: Dd a -> Dd a -> Dd a
  equf0 :: Dd a -> Dd a -> Dd a
  imp :: Dd a -> Dd a -> Dd a
  impf0 :: Dd a -> Dd a -> Dd a
  exists :: Int -> Dd a -> Dd a
  forall :: Int -> Dd a -> Dd a
  existsQ :: Int -> [Prp] -> Dd a -> Dd a
  forallQ :: Int -> [Prp] -> Dd a -> Dd a
  existsSetQ :: [Int] -> [Prp] -> Dd a -> Dd a
  forallSetQ :: [Int] -> [Prp] -> Dd a -> Dd a
  existsSet :: [Int] -> Dd a -> Dd a
  forallSet :: [Int] -> Dd a -> Dd a
  conSet :: [Dd a] -> Dd a
  disSet :: [Dd a] -> Dd a
  xorSet :: [Dd a] -> Dd a
  ifthenelse :: Dd a -> Dd a -> Dd a -> Dd a
  restrict :: Dd a -> (Int,Bool) -> Dd a
  restrictSet :: Dd a -> [(Int,Bool)] -> Dd a
  restrictQ :: Dd a -> [Prp] -> (Int,Bool) -> Dd a
  restrictSetQ :: Dd a -> [Prp] -> [(Int,Bool)] -> Dd a
  restrictQs0 :: Dd a -> [Prp] -> (Int,Bool) -> Dd a
  restrictSetQs0 :: Dd a -> [Prp] -> [(Int,Bool)] -> Dd a
  writeToDot :: Dd a -> String -> IO()
  printDdInfo :: Dd a -> String -> IO()
  returnDot :: Dd a -> String
  returnDot d = unsafePerformIO $ withSystemTempDirectory "smcdel" $ \tmpdir -> do
      writeToDot d (tmpdir ++ "/temp.dot")
      readFile (tmpdir ++ "/temp.dot")
  forceCheckDd :: Dd a -> String -- ugly fix to ensure evaluation of dd
  forceCheckDd d = unsafePerformIO $! do
    withSystemTempDirectory "smcdel" $ \tmpdir -> do
      writeToDot d (tmpdir ++ "/temp.dot")
      readFile (tmpdir ++ "/temp.dot")

--
instance DdF B where
  neg (ToDd b) = ToDd $ Cudd.Cudd.cuddNot manager b
  con (ToDd b1) (ToDd b2) = ToDd $ Cudd.Cudd.cuddBddAnd manager b1 b2
  dis (ToDd b1) (ToDd b2) = ToDd $ Cudd.Cudd.cuddBddOr manager b1 b2
  xor (ToDd b1) (ToDd b2) = ToDd $ Cudd.Cudd.cuddBddXor manager b1 b2
  equ a b = con (imp a b) (imp b a)
  imp (ToDd b1) (ToDd b2) = ToDd $ Cudd.Cudd.cuddBddIte manager b1 b2 t where
    ToDd t = top 
  ifthenelse (ToDd b1) (ToDd b2) (ToDd b3) = ToDd $ Cudd.Cudd.cuddBddIte manager b1 b2 b3
  exists n (ToDd b) = ToDd $ Cudd.Cudd.cuddBddExistAbstract manager b ( Cudd.Cudd.cuddIndicesToCube manager [n])
  forall n (ToDd b) = ToDd $ Cudd.Cudd.cuddBddUnivAbstract manager b ( Cudd.Cudd.cuddIndicesToCube manager [n])
  restrict (ToDd b) (n,bit) = ToDd $ Cudd.Cudd.cuddBddLICompaction manager b res where
    ToDd res = if bit then var n else neg (var n)

  --set versions
  existsSet [] b = b
  existsSet ns (ToDd b) = ToDd $ Cudd.Cudd.cuddBddExistAbstract manager b ( Cudd.Cudd.cuddIndicesToCube manager ns)
    --where correctedns = map (+(-1)) ns
  forallSet [] b = b
  forallSet ns (ToDd b) = ToDd $ Cudd.Cudd.cuddBddUnivAbstract manager b ( Cudd.Cudd.cuddIndicesToCube manager ns)
    --where correctedns = map (+(-1)) ns
  conSet [] = top
  conSet (b:bs) = foldl con b bs
  disSet [] = bot
  disSet (b:bs) = foldl dis b bs
  xorSet [] = bot
  xorSet (b:bs) = foldl xor b bs
  restrictSet (ToDd b) bits = ToDd $ Cudd.Cudd.cuddBddLICompaction manager b res where
    ToDd res = conSet $ map (\(n,bit) -> if bit then var n else neg (var n)) bits
  

  --helper functions
  printDdInfo (ToDd b) str = do
    putStrLn str
    Cudd.Cudd.cuddPrintDdInfo manager b
    return ()
  writeToDot (ToDd b) = Cudd.Cudd.cuddBddToDot manager b


instance DdF Z where
  neg z = ifthenelse z botZ topZ
  negf0 z = ifthenelse z topZ botZ
  con (ToDd z1) (ToDd z2) = ToDd (Cudd.Cudd.cuddZddIntersect manager z1 z2)
  dis (ToDd z1) (ToDd z2) = ToDd (Cudd.Cudd.cuddZddUnion manager z1 z2)
  xor z1 z2 =  a `dis` b where
    a = differenceZ z1 z2 
    b = differenceZ z2 z1
  equ a b = con (imp a b) (imp b a)
  equf0 a b = dis (imp a b) (imp b a)
  imp (ToDd z1) (ToDd z2) = ToDd $ Cudd.Cudd.cuddZddITE manager z1 z2 t where
    ToDd t = topZ
  impf0 z1 z2 = (neg z1) `con` z2
  ifthenelse (ToDd x) (ToDd y) (ToDd z) = ToDd (Cudd.Cudd.cuddZddITE manager x y z)
  exists _ _ = error "exists on zdd needs a context" 

  forall _ _ = error "forall on zdd needs a context"
  restrict _ _ = error "restrict on zdd needs a context"

  existsQ n u zdd = replaceByTop `dis` replaceByBot where
    replaceByTop = productZ (sub1 zdd n) (exceptVarZContext u n)--is this correct?
    replaceByBot = productZ (sub0 zdd n) (exceptVarZContext u n)
  forallQ n u zdd = replaceByTop `con` replaceByBot where
    replaceByTop = productZ (sub1 zdd n) (exceptVarZContext u n)--is this correct?
    replaceByBot = productZ (sub0 zdd n) (exceptVarZContext u n)
  restrictQ zdd u (n,bit) = if bit 
    then productZ (sub1 zdd n) (exceptVarZContext u n) --`debug` "true"
  else productZ (sub0 zdd n) (exceptVarZContext u n)  --`debug` "false" --due to cudd's failure of context mentioning i cannot do productZ (sub0 zdd n) (neg $ onlyZ n)
  restrictQs0 zdd u (n,bit) = if bit 
    then productZ (sub0 zdd n) (exceptVarZContext u n) --`debug` "true"
  else productZ (sub1 zdd n) (exceptVarZContext u n)

  --Set versions
  forallSet [] z = z
  forallSet [n] z = forall n z
  forallSet (n:ns) z = x `dis` forallSet ns x where 
    x = forall n z
  existsSet [] z = z
  existsSet [n] z = exists n z
  existsSet (n:ns) z = x `con` existsSet ns x where --Here we loose more than 1 variable in our vocabulary!!!!
    x = exists n z
  forallSetQ [] _ z = z
  forallSetQ [n] v z = forallQ n v z
  forallSetQ (n:ns) v z = x `dis` forallSetQ ns v x where 
    x = forallQ n v z
  existsSetQ [] _ z = z
  existsSetQ [n] v z = existsQ n v z
  existsSetQ (n:ns) v z = x `con` existsSetQ ns v x where --Here we loose more than 1 variable in our vocabulary!!!!
    x = existsQ n v z
  restrictSetQ z _ [] = z
  restrictSetQ zdd u [n] = restrictQ zdd u n
  restrictSetQ zdd u (n : ns) = restrictSetQ (restrictQ zdd u n) u ns
  restrictSetQs0 z _ [] = z
  restrictSetQs0 zdd u [n] = restrictQs0 zdd u n
  restrictSetQs0 zdd u (n : ns) = restrictSetQs0 (restrictQs0 zdd u n) u ns


  conSet [] = error "empty AND list"
  conSet [z] = z
  conSet (z:zs) = foldl con z zs
  disSet [] = error "empty OR list"
  disSet [z] = z
  disSet (z:zs) = foldl dis z zs
  xorSet [] = error "empty XOR list"
  xorSet [z] = z
  xorSet (z:zs) = foldl xor z zs
  restrictSet _ _ = error "restricting for zdd needs a context"
  

  --helper functions
  printDdInfo (ToDd zdd) str = do
    putStrLn str
    Cudd.Cudd.cuddPrintDdInfo manager zdd
    return ()
  writeToDot (ToDd zdd) = Cudd.Cudd.cuddZddToDot manager zdd



-------- 


gfp :: (Dd B -> Dd B) -> Dd B
gfp operator = gfpLoop top where
  gfpLoop :: Dd B -> Dd B
  gfpLoop current =
    if current == operator current
      then current
      else gfpLoop (operator current)

gfpZ :: (Dd Z -> Dd Z) -> Dd Z
gfpZ operator = gfpLoop topZ where
  gfpLoop :: Dd Z -> Dd Z
  gfpLoop current =
    if current == operator current
      then current
      else gfpLoop (operator current)

gfpZf0 :: (Dd Z -> Dd Z) -> Dd Z
gfpZf0 operator = gfpLoop botZ where
  gfpLoop :: Dd Z -> Dd Z
  gfpLoop current = 
    if current == operator current
      then current 
      else gfpLoop (operator current) 


differenceZ :: Dd Z -> Dd Z -> Dd Z
differenceZ (ToDd x) (ToDd y) = ToDd $ Cudd.Cudd.cuddZddDiff manager x y


initZddVarsWithInt :: [Int] -> Dd Z
initZddVarsWithInt [] = error "initialising empty vocabulary list of zdd vars"
initZddVarsWithInt [n] = varZ (n)
initZddVarsWithInt (n: ns) = varZ (n) `dis` initZddVarsWithInt ns

createZddFromBdd :: Dd B -> Dd Z
createZddFromBdd (ToDd b) = ToDd (Cudd.Cudd.cuddZddPortFromBdd manager b)
  --portVars

portVars :: IO()
portVars = Cudd.Cudd.cuddZddVarFromBdd manager

debug :: c -> String -> c
debug = flip trace
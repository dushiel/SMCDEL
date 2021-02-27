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
  gfp, 
  -- * extra Zdd functionalities
  gfpZ, writeToDot, printDdInfo, differenceZ, portVars, initZddVarsWithInt, topZ, varZ, botZ,
  createZddFromBdd, forceCheckDd, sub0, sub1, productZ, complementZ
) where

import qualified Cudd.Cudd
import System.IO.Unsafe ( unsafePerformIO )
import System.IO.Temp ( withSystemTempDirectory )
import Debug.Trace (trace)
import SMCDEL.Language (Prp)

onlyZ :: Int -> Dd Z
onlyZ n = ToDd $ Cudd.Cudd.cuddZddComplement manager (Cudd.Cudd.cuddZddIthVar manager (n-1))

onlyZquick :: [Prp] -> Int -> Dd Z --ask malvin about the fmap variant something like $>
onlyZquick context n = neg $ conPropsExceptVarZ context n

conPropsExceptVarZ :: [Prp] -> Int -> Dd Z  
conPropsExceptVarZ (n: ns) except 
  | fromEnum n /= except   = varZ (fromEnum n) `con` conPropsExceptVarZ ns except
  | fromEnum n == except   = conPropsExceptVarZ ns except
conPropsExceptVarZ [n] except 
  | fromEnum n /= except   = varZ (fromEnum n)
  | fromEnum n == except   = topZ
conPropsExceptVarZ _ _ = error "empty context list for conPropsExceptVar"

complementZ :: Dd Z -> Dd Z 
complementZ (ToDd z) = ToDd $ Cudd.Cudd.cuddZddComplement manager z

sub0 :: Dd Z -> Int -> Dd Z
sub0 z n = ToDd $ Cudd.Cudd.cuddZddSub0 manager zmin (n-1) where
  ToDd zmin = z
sub1 :: Dd Z -> Int -> Dd Z
sub1 (ToDd z) n = ToDd $ Cudd.Cudd.cuddZddSub1 manager z (n-1) 

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
var n = ToDd (Cudd.Cudd.cuddBddIthVar manager (n-1))

topZ :: Dd Z
topZ = ToDd (Cudd.Cudd.cuddZddReadOne manager)
botZ :: Dd Z
botZ = ToDd (Cudd.Cudd.cuddZddReadZero manager)
varZ :: Int -> Dd Z
varZ n = ToDd (Cudd.Cudd.cuddZddIthVar manager (n-1))

-------------------------------------------------------------------------------------------

class DdF a where
  neg :: Dd a -> Dd a
  con :: Dd a -> Dd a -> Dd a
  dis :: Dd a -> Dd a -> Dd a
  xor :: Dd a -> Dd a -> Dd a
  equ :: Dd a -> Dd a -> Dd a
  imp :: Dd a -> Dd a -> Dd a
  exists :: Int -> Dd a -> Dd a
  forall :: Int -> Dd a -> Dd a
  existsQ :: Int -> Dd a -> [Prp] -> Dd a
  forallQ :: Int -> Dd a -> [Prp] -> Dd a
  existsSet :: [Int] -> Dd a -> Dd a
  forallSet :: [Int] -> Dd a -> Dd a
  existsSetQ :: [Int] -> Dd a -> [Prp] -> Dd a
  forallSetQ :: [Int] -> Dd a -> [Prp] -> Dd a
  conSet :: [Dd a] -> Dd a
  disSet :: [Dd a] -> Dd a
  xorSet :: [Dd a] -> Dd a
  ifthenelse :: Dd a -> Dd a -> Dd a -> Dd a
  restrict :: Dd a -> (Int,Bool) -> Dd a
  restrictSet :: Dd a -> [(Int,Bool)] -> Dd a
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
  exists n (ToDd b) = ToDd $ Cudd.Cudd.cuddBddExistAbstract manager b ( Cudd.Cudd.cuddIndicesToCube manager [n-1])
  forall n (ToDd b) = ToDd $ Cudd.Cudd.cuddBddUnivAbstract manager b ( Cudd.Cudd.cuddIndicesToCube manager [n-1])
  restrict (ToDd b) (n,bit) = ToDd $ Cudd.Cudd.cuddBddLICompaction manager b res where
    ToDd res = if bit then var n else neg (var n)
  existsQ n zdd _ = exists n zdd
  forallQ n zdd _ = forall n zdd

  --set versions
  existsSet [] b = b
  existsSet ns (ToDd b) = ToDd $ Cudd.Cudd.cuddBddExistAbstract manager b ( Cudd.Cudd.cuddIndicesToCube manager correctedns)
    where correctedns = map (+(-1)) ns
  forallSet [] b = b
  forallSet ns (ToDd b) = ToDd $ Cudd.Cudd.cuddBddUnivAbstract manager b ( Cudd.Cudd.cuddIndicesToCube manager correctedns)
    where correctedns = map (+(-1)) ns
  forallSetQ n b _ = forallSet n b
  existsSetQ n b _ = existsSet n b
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
  con (ToDd z1) (ToDd z2) = ToDd (Cudd.Cudd.cuddZddIntersect manager z1 z2)
  dis (ToDd z1) (ToDd z2) = ToDd (Cudd.Cudd.cuddZddUnion manager z1 z2)
  xor z1 z2 =  a `con` b where
    a = differenceZ z1 z2 
    b = differenceZ z2 z1
  equ a b = con (imp a b) (imp b a)
  imp (ToDd z1) (ToDd z2) = ToDd $ Cudd.Cudd.cuddZddITE manager z1 z2 t where
    ToDd t = topZ
  ifthenelse (ToDd x) (ToDd y) (ToDd z) = ToDd (Cudd.Cudd.cuddZddITE manager x y z)
  exists n zdd =  neg $ forall n $ neg zdd --might be a quicker method possible instead of negating forall
  forall n zdd = productZ ((sub0 zdd n) `con` (sub1 zdd n)) (onlyZ n)
  existsQ n zdd context =  neg $ forallQ n (neg zdd) context
  forallQ n zdd context = productZ ((sub0 zdd n) `con` (sub1 zdd n)) (onlyZquick context n)

  restrict zdd (n,bit) = if bit 
    then productZ (sub1 zdd n) (onlyZ n) --`debug` "true"
  else productZ (sub0 zdd n) (onlyZ n) --`debug` "false"
  

  --Set versions
  forallSet [] _ = error "empty UniversalVar list"
  forallSet [n] z = forall n z
  forallSet (n:ns) z = x `dis` forallSet ns x where 
    x = forall n z
  existsSet [] _ = error "empty ExistsVar list"
  existsSet [n] z = exists n z
  existsSet (n:ns) z = x `con` existsSet ns x where --Here we loose more than 1 variable in our vocabulary!!!!
    x = exists n z
  forallSetQ [] _ _ = error "empty UniversalVar list"
  forallSetQ [n] z context = forallQ n z context
  forallSetQ (n:ns) z context = x `dis` forallSetQ ns x context where 
    x = forallQ n z context
  existsSetQ [] _ _ = error "empty ExistsVar list"
  existsSetQ [n] z context = existsQ n z context
  existsSetQ (n:ns) z context = x `con` existsSetQ ns x context where 
    x = existsQ n z context
  conSet [] = error "empty AND list"
  conSet [z] = z
  conSet (z:zs) = foldl con z zs
  disSet [] = error "empty OR list"
  disSet [z] = z
  disSet (z:zs) = foldl dis z zs
  xorSet [] = error "empty XOR list"
  xorSet [z] = z
  xorSet (z:zs) = foldl xor z zs
  restrictSet _ [] = error "restricting with empty list"
  restrictSet zdd [n] = restrict zdd n
  restrictSet zdd (n : ns) = restrictSet (restrict zdd n) ns
  

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
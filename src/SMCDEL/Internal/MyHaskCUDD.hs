module SMCDEL.Internal.MyHaskCUDD (
  -- * Types
  Bdd, Zdd,
  -- * Creation of new BDDs
  top, bot, var,
  -- * Combination and Manipulation of BDDs
  neg, con, dis, imp, equ, xor, conSet, disSet, xorSet,
  exists, forall, forallSet, existsSet,
  restrict, restrictSet,
  ifthenelse,
  gfp,
  -- * Zdd functionalities
  topZ, varZ, createZddFromBdd, differenceZ, intersectionZ, botZ, restrictZ, restrictSetZ,
  negZ, conZ, disZ, impZ, disSetZ, conSetZ, xorZ, xorSetZ,
  existsZ, existsSetZ, forallZ, forallSetZ, equZ, ifthenelseZ, gfpZ, initZddVarsWithInt,
  -- * New helper functions
  writeZdd, writeBdd, printZddInfo, printBddInfo
) where

import qualified Cudd.Cudd
import System.IO.Unsafe


type Bdd =  Cudd.Cudd.DdNode

manager :: Cudd.Cudd.DdManager
manager = Cudd.Cudd.cuddInit

top :: Bdd
top =  Cudd.Cudd.cuddReadOne manager

bot :: Bdd
bot =  Cudd.Cudd.cuddReadLogicZero manager

var :: Int -> Bdd
var =  Cudd.Cudd.cuddBddIthVar manager

neg :: Bdd -> Bdd
neg =  Cudd.Cudd.cuddNot manager

xor :: Bdd -> Bdd -> Bdd
xor =  Cudd.Cudd.cuddBddXor manager

exists :: Int -> Bdd -> Bdd
exists n b =  Cudd.Cudd.cuddBddExistAbstract manager b ( Cudd.Cudd.cuddIndicesToCube manager [n])

forall :: Int -> Bdd -> Bdd
forall n b =  Cudd.Cudd.cuddBddUnivAbstract manager b ( Cudd.Cudd.cuddIndicesToCube manager [n])

existsSet :: [Int] -> Bdd -> Bdd
existsSet [] b = b
existsSet ns b =  Cudd.Cudd.cuddBddExistAbstract manager b ( Cudd.Cudd.cuddIndicesToCube manager ns)

forallSet :: [Int] -> Bdd -> Bdd
forallSet [] b = b
forallSet ns b =  Cudd.Cudd.cuddBddUnivAbstract manager b ( Cudd.Cudd.cuddIndicesToCube manager ns)

equ :: Bdd -> Bdd -> Bdd
equ a b = con (imp a b) (imp b a)

imp :: Bdd -> Bdd -> Bdd
imp b1 b2 =  Cudd.Cudd.cuddBddIte manager b1 b2 top

ifthenelse :: Bdd -> Bdd -> Bdd -> Bdd
ifthenelse =  Cudd.Cudd.cuddBddIte manager

con :: Bdd -> Bdd -> Bdd
con =  Cudd.Cudd.cuddBddAnd manager

dis :: Bdd -> Bdd -> Bdd
dis =  Cudd.Cudd.cuddBddOr manager

conSet :: [Bdd] -> Bdd
conSet [] = top
conSet (b:bs) = foldl con b bs

disSet :: [Bdd] -> Bdd
disSet [] = bot
disSet (b:bs) = foldl dis b bs

xorSet :: [Bdd] -> Bdd
xorSet [] = bot
xorSet (b:bs) = foldl xor b bs

gfp :: (Bdd -> Bdd) -> Bdd
gfp operator = gfpLoop top where
  gfpLoop :: Bdd -> Bdd
  gfpLoop current =
    if current == operator current
      then current
      else gfpLoop (operator current)

restrict :: Bdd -> (Int,Bool) -> Bdd
restrict b (n,bit) =  Cudd.Cudd.cuddBddLICompaction manager b res where
  res = if bit then var n else neg (var n)

restrictSet :: Bdd -> [(Int,Bool)] -> Bdd
restrictSet b bits =  Cudd.Cudd.cuddBddLICompaction manager b res where
  res = conSet $ map (\(n,bit) -> if bit then var n else neg (var n)) bits

--Zdd stuff

newtype Zdd = ToZdd Cudd.Cudd.DdNode deriving (Eq,Show)

topZ :: Zdd
topZ = ToZdd (Cudd.Cudd.cuddZddReadOne manager)

botZ :: Zdd
botZ = ToZdd (Cudd.Cudd.cuddReadLogicZero manager)

varZ :: Int -> Zdd
varZ i = ToZdd (Cudd.Cudd.cuddZddIthVar manager i)

negZ :: Zdd -> [Int] -> Zdd
negZ z v = (initZddVarsWithInt v) `differenceZ` z
  

conZ :: Zdd -> Zdd -> Zdd
conZ (ToZdd x) (ToZdd y) =  ToZdd (Cudd.Cudd.cuddZddIntersect manager x y)

disZ :: Zdd -> Zdd -> Zdd
disZ (ToZdd x) (ToZdd y) =  ToZdd (Cudd.Cudd.cuddZddUnion manager x y)

xorZ :: Zdd -> Zdd -> Zdd 
xorZ x y =  a `conZ` b where
  a = differenceZ x y 
  b = differenceZ y x

conSetZ :: [Zdd] -> Zdd
conSetZ [] = error "empty AND list"
conSetZ [z] = z
conSetZ (z:zs) = foldl conZ z zs

disSetZ :: [Zdd] -> Zdd
disSetZ [] = error "empty OR list"
disSetZ [z] = z
disSetZ (z:zs) = foldl disZ z zs

xorSetZ :: [Zdd] -> Zdd
xorSetZ [] = error "empty XOR list"
xorSetZ [z] = z
xorSetZ (z:zs) = foldl xorZ z zs

impZ :: Zdd -> Zdd -> Zdd
impZ (ToZdd z2) (ToZdd z1) = ToZdd (Cudd.Cudd.cuddZddITE manager z1 z2 t) where
  ToZdd t = topZ

equZ :: Zdd -> Zdd -> Zdd
equZ a b = (impZ a b) `conZ` (impZ b a)

existsZ :: Int -> Zdd -> Zdd
existsZ n (ToZdd zdd) =  x `conZ` y where
  x = ToZdd $ Cudd.Cudd.cuddZddSub0 manager zdd n
  y = ToZdd $ Cudd.Cudd.cuddZddSub0 manager zdd n

forallZ :: Int -> Zdd -> Zdd
forallZ n (ToZdd zdd) =  x `disZ` y where
  x = ToZdd $ Cudd.Cudd.cuddZddSub0 manager zdd n
  y = ToZdd $ Cudd.Cudd.cuddZddSub0 manager zdd n


existsSetZ :: [Int] -> Zdd -> Zdd
existsSetZ [] _ = error "empty ExistsVar list"
existsSetZ [n] z = existsZ n z
existsSetZ (n:ns) z = x `conZ` forallSetZ ns x where 
  x = forallZ n z

forallSetZ :: [Int] -> Zdd -> Zdd
forallSetZ [] _ = error "empty UniversalVar list"
forallSetZ [n] z = forallZ n z
forallSetZ (n:ns) z = x `disZ` forallSetZ ns x where 
  x = forallZ n z

gfpZ :: (Zdd -> Zdd) -> Zdd
gfpZ operator = gfpLoop topZ where
  gfpLoop :: Zdd -> Zdd
  gfpLoop current =
    if current == operator current
      then current
      else gfpLoop (operator current)

ifthenelseZ :: Zdd -> Zdd -> Zdd -> Zdd
ifthenelseZ (ToZdd x) (ToZdd y) (ToZdd z) = ToZdd (Cudd.Cudd.cuddZddITE manager x y z)

differenceZ :: Zdd -> Zdd -> Zdd
differenceZ (ToZdd x) (ToZdd y) = unsafePerformIO $! do
  printZddInfo (ToZdd x) "difference: x - y\n x/query ="
  printZddInfo (ToZdd y) " y/law ="
  let zdd = (ToZdd (Cudd.Cudd.cuddZddDiff manager x y))
  printZddInfo zdd "result"
  return zdd

intersectionZ :: Zdd -> Zdd -> Zdd
intersectionZ (ToZdd x) (ToZdd y) = ToZdd (Cudd.Cudd.cuddZddIntersect manager x y)

restrictZ :: Zdd -> (Int,Bool) -> Zdd
restrictZ (ToZdd zdd) (n,bit) =  ToZdd $ if bit 
  then Cudd.Cudd.cuddZddSub1 manager zdd n 
else Cudd.Cudd.cuddZddSub0 manager zdd n


restrictSetZ :: Zdd -> [(Int,Bool)] -> Zdd
restrictSetZ _ [] = error "restricting with empty list"
restrictSetZ zdd (n : []) = restrictZ zdd n
restrictSetZ zdd (n : ns) = restrictSetZ (restrictZ zdd n) ns

createZddFromBdd :: Bdd -> Zdd
createZddFromBdd bdd = unsafePerformIO $ do 
  let zdd = (ToZdd (Cudd.Cudd.cuddZddPortFromBdd manager bdd))
  return zdd

initZddVarsWithInt :: [Int] -> Zdd
initZddVarsWithInt [] = error "initialising empty vocabulary list of zdd vars"
initZddVarsWithInt (n: []) = varZ n 
initZddVarsWithInt (n: ns) = varZ n `disZ` initZddVarsWithInt ns

---helper functions placed here for now

printZddInfo :: Zdd -> String -> IO()
printZddInfo (ToZdd zdd) str = do
    putStrLn str
    Cudd.Cudd.cuddPrintDdInfo manager zdd

printBddInfo :: Bdd -> IO()
printBddInfo bdd = do
    putStrLn "bdd"
    Cudd.Cudd.cuddPrintDdInfo manager bdd

writeBdd:: Bdd -> String -> IO()
writeBdd bdd f = Cudd.Cudd.cuddBddToDot manager bdd f

writeZdd:: Zdd -> String -> IO()
writeZdd (ToZdd zdd) f = Cudd.Cudd.cuddZddToDot manager zdd f








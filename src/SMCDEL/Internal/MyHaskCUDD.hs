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
  topZ, varZ, differenceZ, botZ, restrictZ, restrictSetZ, portVars, createZddFromBdd,
  negZ, conZ, disZ, impZ, disSetZ, conSetZ, xorZ, xorSetZ,
  existsZ, existsSetZ, forallZ, forallSetZ, equZ, ifthenelseZ, gfpZ, initZddVarsWithInt,
  -- * New helper functions
  writeZdd, writeBdd, printZddInfo, printBddInfo
) where

import qualified Cudd.Cudd
import System.IO.Unsafe

{-}
manager :: Cudd.Cudd.DdManager
manager = Cudd.Cudd.cuddInit

type Bdd =  Cudd.Cudd.DdNode
bot :: Bdd
bot =  Cudd.Cudd.cuddReadLogicZero manager
top :: Bdd
top =  Cudd.Cudd.cuddReadOne manager
var :: Int -> Bdd
var =  Cudd.Cudd.cuddBddIthVar manager

newtype Zdd = ToZdd Cudd.Cudd.DdNode deriving (Eq,Show)
topZ :: Zdd
topZ = ToZdd (Cudd.Cudd.cuddZddReadOne manager)
botZ :: Zdd
botZ = ToZdd (Cudd.Cudd.cuddZddReadZero manager)
varZ :: Int -> Zdd
varZ i = ToZdd (Cudd.Cudd.cuddZddIthVar manager i)

-------------------------------------------------------------------------------------------
class DdF a 
--
instance DdF Bdd -> Bdd where
  neg =  Cudd.Cudd.cuddNot manager

instance DdF Zdd -> Zdd where
  neg = topZ `differenceZ` z

--
instance DdF Bdd -> Bdd -> Bdd where
  con =  Cudd.Cudd.cuddBddAnd manager
  dis =  Cudd.Cudd.cuddBddOr manager
  xor =  Cudd.Cudd.cuddBddXor manager
  equ a b = con (imp a b) (imp b a)
  imp b1 b2 =  Cudd.Cudd.cuddBddIte manager b1 b2 top

instance DdF Zdd -> Zdd -> Zdd where
  con (ToZdd z1) (ToZdd z2) = ToZdd (Cudd.Cudd.cuddZddIntersect manager z1 z2)
  dis (ToZdd z1) (ToZdd z2) = ToZdd (Cudd.Cudd.cuddZddUnion manager z1 z2)
  xor z1 z2 =  a `conZ` b where
    a = differenceZ z1 z2 
    b = differenceZ z2 z1
  equ a b = con (imp a b) (imp b a)
  impZ (ToZdd z1) (ToZdd z2) = ToZdd $ Cudd.Cudd.cuddZddITE manager z1 z1 t where
    ToZdd t = topZ

--
instance DdF Int -> Bdd -> Bdd where
  exists n b =  Cudd.Cudd.cuddBddExistAbstract manager b ( Cudd.Cudd.cuddIndicesToCube manager [n])
  forall n b =  Cudd.Cudd.cuddBddUnivAbstract manager b ( Cudd.Cudd.cuddIndicesToCube manager [n])

instance DdF Int -> Zdd -> Zdd where
  exists n (ToZdd zdd) =  x `dis` y where
    x = ToZdd $ Cudd.Cudd.cuddZddSub0 manager zdd n
    y = ToZdd $ Cudd.Cudd.cuddZddSub1 manager zdd n
  forall n (ToZdd zdd) = ifthenelse (varZ n) x y where
   x = ToZdd $ Cudd.Cudd.cuddZddSub1 manager zdd n
   y = ToZdd $ Cudd.Cudd.cuddZddSub0 manager zdd n 
  
  
--
instance DdF [Int] -> Bdd -> Bdd where
  existsSet [] b = b
  existsSet ns b =  Cudd.Cudd.cuddBddExistAbstract manager b ( Cudd.Cudd.cuddIndicesToCube manager ns)
  forallSet [] b = b
  forallSet ns b =  Cudd.Cudd.cuddBddUnivAbstract manager b ( Cudd.Cudd.cuddIndicesToCube manager ns)

instance DdF [Int] -> Zdd -> Zdd where
  forallSet [] _ = error "empty UniversalVar list"
  forallSet [n] z = forall n z
  forallSet (n:ns) z = x `dis` forallSet ns x where 
    x = forall n z
  existsSetZ [] _ = error "empty ExistsVar list"
  existsSetZ [n] z = exists n z
  existsSetZ (n:ns) z = x `con` forallSet ns x where 
    x = forall n z
  
--
instance DdF [Bdd]-> Bdd where
  conSet [] = top
  conSet (b:bs) = foldl con b bs
  disSet [] = bot
  disSet (b:bs) = foldl dis b bs
  xorSet [] = bot
  xorSet (b:bs) = foldl xor b bs

instance DdF [Zdd]-> Zdd where
  conSet [] = error "empty AND list"
  conSet [z] = z
  conSet (z:zs) = foldl con z zs
  disSet [] = error "empty OR list"
  disSet [z] = z
  disSet (z:zs) = foldl dis z zs
  xorSet [] = error "empty XOR list"
  xorSet [z] = z
  xorSet (z:zs) = foldl xor z zs

--
instance DdF Bdd -> Bdd -> Bdd -> Bdd where
  ifthenelse =  Cudd.Cudd.cuddBddIte manager

instance DdF Zdd -> Zdd -> Zdd -> Zdd where
  ifthenelseZ (ToZdd x) (ToZdd y) (ToZdd z) = ToZdd (Cudd.Cudd.cuddZddITE manager x y z)
----------------------------------------------------------------------------------------------}
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
botZ = ToZdd (Cudd.Cudd.cuddZddReadZero manager)

varZ :: Int -> Zdd
varZ i = ToZdd (Cudd.Cudd.cuddZddIthVar manager i)

negZ :: Zdd -> Zdd
negZ z = topZ `differenceZ` z
  

conZ :: Zdd -> Zdd -> Zdd
conZ (ToZdd z1) (ToZdd z2) = ToZdd (Cudd.Cudd.cuddZddIntersect manager z1 z2)

disZ :: Zdd -> Zdd -> Zdd
disZ (ToZdd z1) (ToZdd z2) = ToZdd (Cudd.Cudd.cuddZddUnion manager z1 z2)

xorZ :: Zdd -> Zdd -> Zdd 
xorZ z1 z2 =  a `conZ` b where
  a = differenceZ z1 z2 
  b = differenceZ z2 z1

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
impZ (ToZdd z1) (ToZdd z2) = ToZdd $ Cudd.Cudd.cuddZddITE manager z1 z2 t where
  ToZdd t = topZ

equZ :: Zdd -> Zdd -> Zdd
equZ a b = (impZ a b) `conZ` (impZ b a)

existsZ :: Int -> Zdd -> Zdd
existsZ n zdd =  negZ $ forallZ n $ negZ $ zdd
  {-(x) `disZ` (y) where
  x = ToZdd $ Cudd.Cudd.cuddZddSub0 manager zdd n
  y = ToZdd $ Cudd.Cudd.cuddZddSub1 manager zdd n-}

forallZ :: Int -> Zdd -> Zdd
forallZ n (ToZdd zdd) = x `disZ` y where
  x = ToZdd $ Cudd.Cudd.cuddZddSub0 manager zdd n
  y = ToZdd $ Cudd.Cudd.cuddZddChange manager (Cudd.Cudd.cuddZddSub1 manager zdd n) n 
  
{-divideZ :: Zdd -> Zdd -> Zdd
divideZ (ToZdd z1) (ToZdd z2) = ToZdd (Cudd.Cudd.cuddZddDivide manager z1 z2)-}

existsSetZ :: [Int] -> Zdd -> Zdd
existsSetZ [] _ = error "empty ExistsVar list"
existsSetZ [n] z = existsZ n z
existsSetZ (n:ns) z = x `disZ` existsSetZ ns x where 
  x = forallZ n z

forallSetZ :: [Int] -> Zdd -> Zdd
forallSetZ [] _ = error "empty UniversalVar list"
forallSetZ [n] z = forallZ n z
forallSetZ (n:ns) z = x `conZ` forallSetZ ns x where 
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
differenceZ (ToZdd x) (ToZdd y) = ToZdd (Cudd.Cudd.cuddZddDiff manager x y)

restrictZ :: Zdd -> (Int,Bool) -> Zdd
restrictZ (ToZdd zdd) (n,bit) =  ToZdd $ if bit 
  then Cudd.Cudd.cuddZddSub1 manager zdd n 
else Cudd.Cudd.cuddZddSub0 manager zdd n

restrictSetZ :: Zdd -> [(Int,Bool)] -> Zdd
restrictSetZ _ [] = error "restricting with empty list"
restrictSetZ zdd (n : []) = restrictZ zdd n
restrictSetZ zdd (n : ns) = restrictSetZ (restrictZ zdd n) ns

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

createZddFromBdd :: Bdd -> Zdd
createZddFromBdd bdd = (ToZdd (Cudd.Cudd.cuddZddPortFromBdd manager bdd))

portVars :: IO()
portVars = Cudd.Cudd.cuddZddVarFromBdd manager

{-}


applyToDd :: dd -> DdF ( ToZddF a -> zdd | ToBddF a -> bdd) -> dd
printDdInfo (ToZdd z) (ToZddF zddFunc) = Dd zddFunc z
printDdInfo (ToBdd b) (ToBddF bddFunc) = Dd bddFunc b

printDdInfo :: (zdd -> zdd | bdd -> bdd)
printDdInfo = ()

-}



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
  gfpZ, writeToDot, printDdInfo, differenceZ, portVars, initZddVarsWithInt, topZ, varZ, botZ,
  createZddFromBdd
) where

import qualified Cudd.Cudd
import System.IO.Unsafe


manager :: Cudd.Cudd.DdManager
manager = Cudd.Cudd.cuddInit

{-}
newtype Dd x = ToDd (Cudd.Cudd.DdNode)
data B
data Z

bot2 :: Dd B 
bot2 = ToDd (Cudd.Cudd.cuddReadLogicZero manager)
-}

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
class DdF a where
  neg :: a -> a
  con :: a -> a -> a
  dis :: a -> a -> a
  xor :: a -> a -> a
  equ :: a -> a -> a
  imp :: a -> a -> a
  exists :: Int -> a -> a
  forall :: Int -> a -> a
  existsSet :: [Int] -> a -> a
  forallSet :: [Int] -> a -> a
  conSet :: [a] -> a
  disSet :: [a] -> a
  xorSet :: [a] -> a
  ifthenelse :: a -> a -> a -> a
  restrict :: a -> (Int,Bool) -> a
  restrictSet :: a -> [(Int,Bool)] -> a
  writeToDot :: a -> String -> IO()
  printDdInfo :: a -> String -> IO()


--
instance DdF Cudd.Cudd.DdNode where
  neg =  Cudd.Cudd.cuddNot manager
  con =  Cudd.Cudd.cuddBddAnd manager
  dis =  Cudd.Cudd.cuddBddOr manager
  xor =  Cudd.Cudd.cuddBddXor manager
  equ a b = con (imp a b) (imp b a)
  imp b1 b2 =  Cudd.Cudd.cuddBddIte manager b1 b2 top
  ifthenelse =  Cudd.Cudd.cuddBddIte manager
  exists n b =  Cudd.Cudd.cuddBddExistAbstract manager b ( Cudd.Cudd.cuddIndicesToCube manager [n])
  forall n b =  Cudd.Cudd.cuddBddUnivAbstract manager b ( Cudd.Cudd.cuddIndicesToCube manager [n])
  restrict b (n,bit) =  Cudd.Cudd.cuddBddLICompaction manager b res where
    res = if bit then var n else neg (var n)

  --set versions
  existsSet [] b = b
  existsSet ns b =  Cudd.Cudd.cuddBddExistAbstract manager b ( Cudd.Cudd.cuddIndicesToCube manager ns)
  forallSet [] b = b
  forallSet ns b =  Cudd.Cudd.cuddBddUnivAbstract manager b ( Cudd.Cudd.cuddIndicesToCube manager ns)
  conSet [] = top
  conSet (b:bs) = foldl con b bs
  disSet [] = bot
  disSet (b:bs) = foldl dis b bs
  xorSet [] = bot
  xorSet (b:bs) = foldl xor b bs
  restrictSet b bits =  Cudd.Cudd.cuddBddLICompaction manager b res where
    res = conSet $ map (\(n,bit) -> if bit then var n else neg (var n)) bits
  

  --helper functions
  printDdInfo bdd str = do
    putStrLn str
    Cudd.Cudd.cuddPrintDdInfo manager bdd
  writeToDot bdd f = Cudd.Cudd.cuddBddToDot manager bdd f


instance DdF Zdd where
  neg z = topZ `differenceZ` z
  con (ToZdd z1) (ToZdd z2) = ToZdd (Cudd.Cudd.cuddZddIntersect manager z1 z2)
  dis (ToZdd z1) (ToZdd z2) = ToZdd (Cudd.Cudd.cuddZddUnion manager z1 z2)
  xor z1 z2 =  a `con` b where
    a = differenceZ z1 z2 
    b = differenceZ z2 z1
  equ a b = con (imp a b) (imp b a)
  imp (ToZdd z1) (ToZdd z2) = ToZdd $ Cudd.Cudd.cuddZddITE manager z1 z2 t where
    ToZdd t = topZ
  ifthenelse (ToZdd x) (ToZdd y) (ToZdd z) = ToZdd (Cudd.Cudd.cuddZddITE manager x y z)
  exists n zdd =  neg $ forall n $ neg $ zdd
  forall n (ToZdd zdd) = x `dis` y where
    x = ToZdd $ Cudd.Cudd.cuddZddSub0 manager zdd n
    y = ToZdd $ Cudd.Cudd.cuddZddChange manager (Cudd.Cudd.cuddZddSub1 manager zdd n) n
  restrict (ToZdd zdd) (n,bit) =  ToZdd $ if bit 
    then Cudd.Cudd.cuddZddChange manager (Cudd.Cudd.cuddZddSub1 manager zdd n) n
  else Cudd.Cudd.cuddZddSub0 manager zdd n

  --Set versions
  forallSet [] _ = error "empty UniversalVar list"
  forallSet [n] z = forall n z
  forallSet (n:ns) z = x `dis` forallSet ns x where 
    x = forall n z
  existsSet [] _ = error "empty ExistsVar list"
  existsSet [n] z = exists n z
  existsSet (n:ns) z = x `con` forallSet ns x where 
    x = forall n z
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
  restrictSet zdd (n : []) = restrict zdd n
  restrictSet zdd (n : ns) = restrictSet (restrict zdd n) ns
  

  --helper functions
  printDdInfo (ToZdd zdd) str = do
    putStrLn str
    Cudd.Cudd.cuddPrintDdInfo manager zdd
  writeToDot (ToZdd zdd) f = Cudd.Cudd.cuddZddToDot manager zdd f

gfp :: (Bdd -> Bdd) -> Bdd
gfp operator = gfpLoop top where
  gfpLoop :: Bdd -> Bdd
  gfpLoop current =
    if current == operator current
      then current
      else gfpLoop (operator current)

gfpZ :: (Zdd -> Zdd) -> Zdd
gfpZ operator = gfpLoop topZ where
  gfpLoop :: Zdd -> Zdd
  gfpLoop current =
    if current == operator current
      then current
      else gfpLoop (operator current)


differenceZ :: Zdd -> Zdd -> Zdd
differenceZ (ToZdd x) (ToZdd y) = ToZdd (Cudd.Cudd.cuddZddDiff manager x y)


initZddVarsWithInt :: [Int] -> Zdd
initZddVarsWithInt [] = error "initialising empty vocabulary list of zdd vars"
initZddVarsWithInt (n: []) = varZ n 
initZddVarsWithInt (n: ns) = varZ n `dis` initZddVarsWithInt ns

createZddFromBdd :: Bdd -> Zdd
createZddFromBdd bdd = (ToZdd (Cudd.Cudd.cuddZddPortFromBdd manager bdd))

portVars :: IO()
portVars = Cudd.Cudd.cuddZddVarFromBdd manager



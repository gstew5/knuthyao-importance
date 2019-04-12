{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, GADTs, RankNTypes #-}
module Main where

import Data.List (union, intersectBy, sort, findIndices)
import Data.Maybe (catMaybes, mapMaybe)
import System.Random
import Data.Char (intToDigit)
import Numeric (floatToDigits)

data Tree r a =
    Leaf a 
  | Split (Tree r a) (Tree r a)
  | Corec (Tree r a -> Tree r a)
  | Never
  | Scale r (Tree r a)

-- Taylor expansion:
eapprox :: Fractional r => Int -> Int -> r
eapprox x 0 = 1
eapprox x n | n > 0 = fromIntegral (x^n) / fromIntegral (fact n) + eapprox x (n-1)
  where fact :: Int -> Integer
        fact 0 = 1
        fact k | k > 0 = fromIntegral k * fact (k - 1)  

e :: Fractional r => a -> a -> Tree r a
e a1 a2 = undefined -- tree that returns a1 with probability (e - 2) and a2 with probability (1 - (e - 2)). 

dgd :: Fractional r => r -> Tree r a
dgd sigma = undefined -- tree that samples from discrete gaussian with \mu = 0, \sigma = sigma

two_third :: a -> a -> Tree r a
two_third a1 a2 = Corec (\rest -> Split (Leaf a1) (Split (Leaf a2) rest))

is_never :: Tree r a -> Bool
is_never Never = True
is_never _ = False

prefix :: Int -> Tree r a -> Tree r a
prefix 0 _ = Never
prefix n t | n > 0 =
  case t of
   Leaf a -> Leaf a
   Split t1 t2 -> Split (prefix (n-1) t1) (prefix (n-1) t2)
   Corec f -> prefix n (f (Corec f))
   Never -> Never
   Scale r t -> Scale r (prefix (n-1) t)

instance (Show r, Show a) => Show (Tree r a) where
  show (Leaf a) = show a
  show (Split t1 t2) = "split (" ++ show t1 ++ ", " ++ show t2 ++ ")"
  show (Corec f) = "corec <..>"
  show Never = "never"
  show (Scale r t) = show r ++ "*(" ++ show t ++ ")"

instance Functor (Tree r) where
  fmap g (Leaf a) = Leaf (g a)
  fmap g (Split t1 t2) = Split (fmap g t1) (fmap g t2)
  fmap g (Corec f) = fmap g (f (Corec f))
  fmap g Never = Never
  fmap g (Scale r t) = Scale r (fmap g t)

instance Num r => Applicative (Tree r) where
  pure a = Leaf a
  Leaf f <*> Leaf a = Leaf (f a)
  Split f1 f2 <*> Split t1 t2 = Split (f1 <*> t1) (f2 <*> t2)
  Corec f <*> Corec t = f (Corec f) <*> t (Corec t)
  Never <*> Never = Never
  Scale r1 f <*> Scale r2 t = Scale (r1*r2) (f <*> t)
  _ <*> _ = Never

bind :: (a -> Tree r b) -> Tree r a -> Tree r b
bind g (Leaf a) = g a
bind g (Split t1 t2) = Split (bind g t1) (bind g t2)
bind g (Corec f) = bind g (f (Corec f))
bind g Never = Never
bind g (Scale r t) = Scale r (bind g t)

instance Num r => Monad (Tree r) where
  (>>=) t g = bind g t
  return a = pure a

list2tree :: [[a]] -> Tree r a
list2tree ls = go 1 ls
  where
    go _ [] = error "Help!"
    go n ([] : rest) = go (2*n) rest
    go n ([a] : rest) = Split (Leaf a) (go (2*n) rest)
    go n ([a,b] : rest) = Split (Leaf a) (Leaf b)
    go n (l : rest) = Split (go (2*n) (take n l : rest)) (go (2*n) (drop n l : rest))

type Bits = [Bool]

type Obs a r = (a -> r)

type Sampler a = Bits -> (a, Bits)

sample_many :: Sampler a -> Sampler [a] -> Int -> Sampler [a]
sample_many sampler acc 0 = acc
sample_many sampler acc n | n > 0 =
  sample_many sampler
    (\bits -> let (a, rest1) = sampler bits in
              let (as, rest2) = acc rest1 in
              (a : as, rest2)) (n-1)

sample :: Fractional r => Obs a r -> Tree r a -> Sampler (Maybe r)
sample f (Leaf a) bits = (Just $ f a, bits)
sample f (Split t1 _) (False : bits) = sample f t1 bits
sample f (Split _ t2) (True : bits)  = sample f t2 bits
sample f (Corec h) bits = sample f (h (Corec h)) bits
sample _ Never bits = (Nothing, bits)
sample f (Scale r t) bits = let (rt, rest) = sample f t bits in (fmap ((*) r) rt, rest)

type Name = String

data Val =
    VFloat Float
  | VBool Bool
    deriving (Show, Eq)

instance Num Val where
  (+) (VFloat r1) (VFloat r2) = VFloat (r1 + r2)
  (+) _ _ = error "ill-typed addition"
  (-) (VFloat r1) (VFloat r2) = VFloat (r1 - r2)
  (-) _ _ = error "ill-typed subtraction"  
  (*) (VFloat r1) (VFloat r2) = VFloat (r1 * r2)
  (*) _ _ = error "ill-typed multiplication"    
  abs (VFloat r) = VFloat (abs r)
  abs _ = error "ill-typed absolute value"
  signum (VFloat r) = VFloat (signum r)
  signum _ = error "ill-typed signum"
  fromInteger i = VFloat (fromInteger i)

instance Fractional Val where
  fromRational r = VFloat (fromRational r)
  (/) (VFloat r1) (VFloat r2) = VFloat (r1 / r2)
  (/) _ _ = error "ill-typed fractional division"

instance Floating Val where
  pi = VFloat pi
  exp (VFloat r) = VFloat (exp r)
  exp _ = error "ill-typed exp"
  log (VFloat r) = VFloat (log r)
  log _ = error "ill-typed log"
  sqrt (VFloat r) = VFloat (sqrt r)
  sqrt _ = error "ill-typed sqrt"
  (**) (VFloat r1) (VFloat r2) = VFloat (r1 ** r2)
  (**) _ _ = error "ill-typed (**)"
  logBase (VFloat r1) (VFloat r2) = VFloat (logBase r1 r2)
  logBase _ _ = error "ill-typed logBase"
  sin (VFloat r) = VFloat (sin r)
  sin _ = error "ill-typed sin"
  cos (VFloat r) = VFloat (cos r)
  cos _ = error "ill-typed cos"
  tan (VFloat r) = VFloat (tan r)
  tan _ = error "ill-typed tan"
  asin (VFloat r) = VFloat (asin r)
  asin _ = error "ill-typed asin"
  acos (VFloat r) = VFloat (acos r)
  acos _ = error "ill-typed acos"
  atan (VFloat r) = VFloat (atan r)
  atan _ = error "ill-typed atan"
  sinh (VFloat r) = VFloat (sinh r)
  sinh _ = error "ill-typed sinh"
  cosh (VFloat r) = VFloat (cosh r)
  cosh _ = error "ill-typed cosh"
  asinh (VFloat r) = VFloat (asinh r)
  asinh _ = error "ill-typed asinh"
  acosh (VFloat r) = VFloat (acosh r)
  acosh _ = error "ill-typed acosh"
  atanh (VFloat r) = VFloat (atanh r)
  atanh _ = error "ill-typed atanh"

instance Ord Val where
  compare (VFloat r1) (VFloat r2) = compare r1 r2
  compare (VBool False) (VBool True) = LT
  compare (VBool True) (VBool False) = GT
  compare (VBool _) (VBool _) = EQ
  compare (VBool _) (VFloat _) = LT
  
type St = [(Name, Val)]

empty :: St
empty = []

upd :: Name -> Val -> St -> St
upd x v st = (x,v) : st

get :: Name -> St -> Val
get x [] = error "name not bound"
get x ((y, v) : rest) = if x==y then v else get x rest

data Exp = 
    EVal Val
  | EVar Name
  | EEq Exp Exp
  | ELt Exp Exp
  | EPlus Exp Exp

einterp :: Exp -> St -> Val
einterp (EVal v) _ = v
einterp (EVar x) st = get x st
einterp (EEq e1 e2) st =
  case (einterp e1 st, einterp e2 st) of
    (VFloat r1, VFloat r2) -> VBool (r1 == r2)
    (_, _) -> error "ill-typed expression"
einterp (ELt e1 e2) st =
  case (einterp e1 st, einterp e2 st) of
    (VFloat r1, VFloat r2) -> VBool (r1 < r2)
    (_, _) -> error "ill-typed expression"
einterp (EPlus e1 e2) st =
  case (einterp e1 st, einterp e2 st) of
    (VFloat r1, VFloat r2) -> VFloat (r1 + r2)
    (_, _) -> error "ill-typed expression"

is_true :: Exp -> St -> Bool
is_true e st =
  case einterp e st of
    VBool b -> b
    _ -> error "not a Boolean"

type Pattern = forall r a. Tree r a -> Tree r a -> Tree r a

data Com where 
  Skip :: Com
  Abort :: Com
  Combine :: Pattern -> Com -> Com -> Com  
  Assign :: Name -> Exp -> Com
  Seq :: Com -> Com -> Com
  Ite :: Exp -> Com -> Com -> Com

-- Derived commands:
  Flip :: Com -> Com -> Com  
  Observe :: Exp -> Com
  While :: Exp -> Com -> Com

interp :: Com -> Tree r St -> Tree r St
interp Skip t = t
interp Abort t = bind (\_ -> Never) t
interp (Combine p c1 c2) t = bind (\st -> p (interp c1 (Leaf st)) (interp c2 (Leaf st))) t
interp (Assign x e) t = bind (\st -> Leaf $ upd x (einterp e st) st) t
interp (Seq c1 c2) t = interp c2 (interp c1 t)
interp (Ite e c1 c2) t = bind (\st -> if is_true e st then interp c1 (Leaf st) else interp c2 (Leaf st)) t

-- Derived commands:
interp (Flip c1 c2) t = interp (Combine Split c1 c2) t
interp (Observe e) t = interp (Ite e Skip Abort) t
interp (While e c) t =
  mu (\f t -> bind (\st -> if is_true e st then f (interp c (Leaf st))
                           else Leaf st) t) t

mu :: ((Tree r a -> Tree r a) -> (Tree r a -> Tree r a)) -> (Tree r a -> Tree r a)
mu f = f (mu f)

opt :: Fractional r => Tree r a -> Tree r a
opt (Leaf a) = Leaf a
opt (Split t1 t2) | is_never (opt t1) && is_never (opt t2) = Never
opt (Split t1 t2) | is_never (opt t1) = opt t2
opt (Split t1 t2) | is_never (opt t2) = opt t1
opt (Split t1 t2) | otherwise = Split (opt t1) (opt t2)
opt (Corec f) | is_never (opt (f (Corec f))) = Never
opt (Corec f) | otherwise = opt (f (Corec f))
opt Never = Never
opt (Scale r t) | is_never (opt t) = Never
opt (Scale r t) | otherwise = Scale r $ opt t

infer :: Fractional r => Int -> Obs St r -> Com -> Tree r St -> Sampler (Maybe r)
--infer d f c t bits = sample f (opt $ prefix d $ interp c t) bits
infer d f c t bits = sample f (interp c t) bits

run_tree :: Floating r => Obs s r -> Tree r s -> Int -> Int -> IO ([r], r, r, (r, r))
run_tree f t d n = do
  g <- newStdGen
  let bits = randoms g :: [Bool]
  let sampler = sample f t
  let (msamples, remaining_bits) = sample_many sampler (\bits -> ([], bits)) n bits
  let samples = catMaybes msamples
  let m = fromIntegral $ length samples
  let mqhat = foldl (+) 0.0 samples / m
  let sqhat = foldl (\b a -> b + (a - mqhat)*(a - mqhat)) 0.0 samples / m
  let bound = (2.58*sqhat)/(sqrt m)
  let confidence = (mqhat - bound, mqhat + bound)
  return (samples, m, bound, confidence)

run :: Floating r => Obs St r -> Com -> Tree r St -> Int -> Int -> IO (r, r, (r, r))
run f c tinit d n = do
  g <- newStdGen
  let bits = randoms g :: [Bool]
  let sampler = infer d f c tinit
  let (msamples, remaining_bits) = sample_many sampler (\bits -> ([], bits)) n bits
  let samples = catMaybes msamples
  let m = fromIntegral $ length samples
  let mqhat = foldl (+) 0.0 samples / m
  let sqhat = foldl (\b a -> b + (a - mqhat)*(a - mqhat)) 0.0 samples / m
  let bound = (2.58*sqhat)/(sqrt m)
  let confidence = (mqhat - bound, mqhat + bound)
  return (m, bound, confidence)

com1 :: Com
com1 =
  Seq
  (Flip
   (Assign "x" (EVal (VFloat 3)))
   (Flip
    (Assign "x" (EVal (VFloat 4)))
    (Assign "x" (EVal (VFloat 5)))))
  (Observe (ELt (EVal (VFloat 3)) (EVar "x")))

ex1 = run (get "x") com1 (Leaf empty) 10
  
com2 :: Com
com2 =
  Ite (EEq (EVar "x") (EVal (VFloat 3)))
    (Flip (Assign "x" (EVal (VFloat 3))) (Assign "x" (EVal (VFloat 4))))
    (Assign "x" (EVal (VFloat 3)))

tinit2 f = (Leaf (upd "x" (VFloat f) empty))
ex2 = run (get "x") com2 (tinit2 3) 10
ex2b = run (get "x") com2 (Split (tinit2 3) (tinit2 4)) 10

-- The expected number of heads (failures) of a fair coin (0.5/(1-0.5) = 1)
com3 :: Com
com3 =
  Seq (Assign "x" (EVal (VFloat 0))) $  
  Seq (Assign "failures" (EVal (VFloat 0))) $
  While (EEq (EVar "x") (EVal (VFloat 0)))
   (Flip
     (Assign "failures" (EPlus (EVar "failures") (EVal (VFloat 1))))
     (Assign "x" (EVal (VFloat 1))))

ex3 = run (get "failures") com3 (Leaf empty) 10

-- The expected number of heads (failures) of a (2/3,1/3) biased coin (0.5/(1-0.5) = 1)
com3_biased :: Com
com3_biased =
  Seq (Assign "x" (EVal (VFloat 0))) $  
  Seq (Assign "failures" (EVal (VFloat 0))) $
  While (EEq (EVar "x") (EVal (VFloat 0)))
   (Combine biased
     (Assign "failures" (EPlus (EVar "failures") (EVal (VFloat 1))))
     (Assign "x" (EVal (VFloat 1))))
  where biased t1 t2 = Corec (\t -> Split t1 (Split t2 t))

ex3_biased = run (get "failures") com3_biased (Leaf empty) 10

-- The uniform distribution over three events
unif3 :: Name -> Com
unif3 x =
  Combine one_third (Assign x (EVal (VFloat 1)))
    (Flip (Assign x (EVal (VFloat 2)))
          (Assign x (EVal (VFloat 3))))
  where one_third t1 t2 = Corec (\t -> Split t2 (Split t1 t))
ex_unif3 = run (get "x") (unif3 "x") (Leaf empty) 10

-- Anindya's slicing example
slice1 :: Com
slice1 =
  Seq (unif3 "x") $
  Seq (unif3 "y") $
  Observe (ELt (EVal (VFloat 1)) (EVar "y"))
ex_slice1 = run (get "x") slice1 (Leaf empty) 10

-- Slice wrt. x
slice1_x :: Com
slice1_x =
  Seq (unif3 "x") Skip
ex_slice1_x = run (get "x") slice1 (Leaf empty) 10

-- An even smaller slicing example
slice0 :: Com
slice0 =
  Seq (unif01 "x") $
  Seq (unif01 "y") $
  Observe (EEq (EPlus (EVar "x") (EVar "y")) (EVal (VFloat 1)))
  where unif01 x = Flip (Assign x (EVal (VFloat 0))) (Assign x (EVal (VFloat 1)))
ex_slice0 = run (get "x") slice0 (Leaf empty) 10

slice0_x :: Com
slice0_x =
  unif01 "x"
  where unif01 x = Flip (Assign x (EVal (VFloat 0))) (Assign x (EVal (VFloat 1)))
ex_slice0_x = run (get "x") slice0_x (Leaf empty) 10

         


-- Discrete Gaussians
-- This construction comes from Section 5 of:
-- SAMPLING FROM DISCRETE GAUSSIANS FOR LATTICE-BASED CRYPTOGRAPHY ON A CONSTRAINED DEVICE
-- by Dwarakanath and Galbraith
a 0 = 1 
a x | x > 0 = c * a (x-1) * b (x-1) * b (x-1) -- exp(-x^2)
b 0 = 1 
b x | x > 0 = c * b (x-1) -- exp(-x)
c = exp (-1)

float2bits :: (RealFloat a, Show a) => a -> Bits
float2bits x =
  if x >= 1.0 then error $ "float2bits: argument " ++ show x ++ " must be <= 1.0" 
  else let (d,e) = floatToDigits 2 x in map to_bit $ shift e d
  where shift 0 d = d
        shift n d | n < 0 = shift (n+1) (0 : d)
        to_bit 0 = False
        to_bit 1 = True

-- ASSUMES: k>=1
pdg_pmf :: Int -> Double -> [Int -> Bool]
pdg_pmf k sigma = [to_fun (x / normalizing_constant) | x <- unnormalized]
  where unnormalized = [f $ fromIntegral x | x <- [0..k-1]]
        f x = exp(-(x*x) / (2*sigma*sigma))
        normalizing_constant = sum unnormalized
        to_fun d i | i >= length (float2bits d) = False
        to_fun d i | i < length (float2bits d) = float2bits d !! i

pdg :: Int -> Double -> Int -> Tree r Int
pdg k sigma prec = list2tree [entries i | i <- [0..prec-1]]
  where entries i = findIndices (\g -> g i) (pdg_pmf k sigma)

main = do
  r <- ex_unif3 1000000
  putStrLn $ show r

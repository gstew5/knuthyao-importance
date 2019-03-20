{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Tree2 where

import Data.List (union, intersectBy, sort)
import Data.Maybe (catMaybes, mapMaybe)
import System.Random

data Tree r a =
    Leaf a
  | Scale r (Tree r a)
  | Split (Tree r a) (Tree r a)
  | Corec (Tree r a -> Tree r a)
  | Never

is_never :: Tree r a -> Bool
is_never Never = True
is_never _ = False

instance (Show r, Show a) => Show (Tree r a) where
  show (Leaf a) = show a
  show (Scale r t) = show r ++ "*(" ++ show t ++ ")"
  show (Split t1 t2) = "split (" ++ show t1 ++ ", " ++ show t2 ++ ")"
  show (Corec f) = "corec <..>"
  show Never = "never"

instance Functor (Tree r) where
  fmap g (Leaf a) = Leaf (g a)
  fmap g (Scale r t) = Scale r (fmap g t)
  fmap g (Split t1 t2) = Split (fmap g t1) (fmap g t2)
  fmap g (Corec f) = fmap g (f (Corec f))
  fmap g Never = Never

instance Num r => Applicative (Tree r) where
  pure a = Leaf a
  Leaf f <*> Leaf a = Leaf (f a)
  Scale r1 f <*> Scale r2 t = Scale (r1*r2) (f <*> t)
  Split f1 f2 <*> Split t1 t2 = Split (f1 <*> t1) (f2 <*> t2)
  Corec f <*> Corec t = f (Corec f) <*> t (Corec t)
  Never <*> Never = Never
  _ <*> _ = Never

bind :: (a -> Tree r b) -> Tree r a -> Tree r b
bind g (Leaf a) = g a
bind g (Scale r t) = Scale r (bind g t)
bind g (Split t1 t2) = Split (bind g t1) (bind g t2)
bind g (Corec f) = bind g (f (Corec f))
bind g Never = Never

instance Num r => Monad (Tree r) where
  (>>=) t g = bind g t
  return a = pure a

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
sample f (Scale r t) bits = let (rt, rest) = sample f t bits in (fmap ((*) r) rt, rest)
sample f (Split t1 _) (False : bits) = sample f (Scale (1/2) t1) bits
sample f (Split _ t2) (True : bits)  = sample f (Scale (1/2) t2) bits
sample f (Corec h) bits = sample f (h (Corec h)) bits
sample _ Never bits = (Nothing, bits)

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

data Atom = AVar Name | AVal Val deriving (Show, Eq)
data Binop = Eq | Neq | Lt | Geq deriving (Show, Eq, Ord)
data Constraint = CBin Binop Atom Atom deriving (Show, Eq)
type Pred = [[Constraint]] -- DNF

cneg :: Constraint -> Constraint
cneg (CBin Eq a1 a2) = CBin Neq a1 a2
cneg (CBin Neq a1 a2) = CBin Eq a1 a2
cneg (CBin Lt a1 a2) = CBin Geq a1 a2
cneg (CBin Geq a1 a2) = CBin Lt a1 a2

instance Ord Atom where
  compare (AVar x) (AVar y) = compare x y
  compare (AVal _) (AVar _) = LT
  compare (AVar _) (AVal _) = GT
  compare (AVal v1) (AVal v2) = compare v1 v2

instance Ord Constraint where
  compare (CBin o1 a1 a2) (CBin o2 b1 b2) =
    case compare o1 o2 of
      EQ -> case compare a1 b1 of
              EQ -> compare a2 b2
              l@_ -> l
      l@_ -> l

subst :: Name -> Val -> Constraint -> Constraint
subst x v (CBin op a1 a2) = CBin op (asubst x v a1) (asubst x v a2)

asubst :: Name -> Val -> Atom -> Atom
asubst x v (AVar y) = if x==y then AVal v else AVar y
asubst x v (AVal vy) = AVal vy

data Polarity = Pos | Neg deriving (Show, Eq, Ord)

type Clause = [(Name, (Val, Polarity))]

negates :: (Name, (Val, Polarity)) -> (Name, (Val, Polarity)) -> Bool
negates (x1, (v1, p1)) (x2, (v2, p2)) = x1==x2 && v1==v2 && p1/=p2

negated_in :: Clause -> (Name, (Val, Polarity)) -> Bool
negated_in as a2 = any (negates a2) as

solve_disjuncts :: Pred -> [Clause]
solve_disjuncts ds = mapMaybe (go []) (map sort ds)
  where go :: Clause -> [Constraint] -> Maybe Clause
        go binds [] = Just binds

        -- Ground constraints:
        go binds (CBin Eq (AVal vx) (AVal vy) : rest) = if vx==vy then go binds rest else Nothing
        go binds (CBin Neq (AVal vx) (AVal vy) : rest) = if vx/=vy then go binds rest else Nothing        
        go binds (CBin Lt (AVal vx) (AVal vy) : rest) = if vx<vy then go binds rest else Nothing

        -- (In-)Equality constraints:
        go binds (CBin Eq (AVar x) (AVal v) : rest) =
          let bind = (x, (v, Pos)) in 
          if negated_in binds bind then Nothing
          else go (bind : binds) (map (subst x v) rest)
        go binds (CBin Eq (AVal v) (AVar x) : rest) = go binds (CBin Eq (AVar x) (AVal v) : rest)
        go binds (CBin Neq (AVar x) (AVal v) : rest) =
          let bind = (x, (v, Neg)) in 
          if negated_in binds bind then Nothing
          else go (bind : binds) rest
        go binds (CBin Neq (AVal v) (AVar x) : rest) = go binds (CBin Neq (AVar x) (AVal v) : rest)

        -- The remaining constraints aren't yet supported:
        go binds (c : _) = error $ "constraint " ++ show c ++ " not yet supported"

simplify :: [Clause] -> [Clause]
simplify [] = []
simplify (c : cs) =
  case hd of
    [] -> [[]]
    _ : _ -> hd : simplify tl
  where hd = filter (not . negated_in_any cs) c
        tl = map (filter (not . negated_in c)) cs
        negated_in_any cs a = any (\as -> negated_in as a) cs

solve :: Pred -> [Clause]
solve cs = simplify $ solve_disjuncts cs

reduce :: Tree r Pred -> Tree r Pred
reduce = bind (\p -> case solve p of
                [] -> Never
                (_ : _) -> Leaf p) -- At least one disjunct is satisfiable.

mget :: Name -> Pred -> Maybe (Val, Polarity)
mget x p = do
  case solve p of
    [] -> Nothing
    (m : _) -> lookup x m -- FIXME: There may be multiple solutions.

get :: Name -> Pred -> (Val, Polarity)
get x p =
  case mget x p of
    Nothing -> error $ "name " ++ x ++ " not bound"
    Just vp -> vp
  
data Com =
    Flip Com Com
  | Nondet Com Com     
  | Observe Pred
  | Assign Name Atom
  | Seq Com Com

-- Derived commands:
ite :: Constraint -> Com -> Com -> Com
ite phi c1 c2 = Nondet (Seq (Observe [[phi]]) c1) (Seq (Observe [[cneg phi]]) c2)

interp :: Num r => Com -> Tree r Pred
interp (Flip c1 c2) = Split (interp c1) (interp c2)
interp (Nondet c1 c2) = do
  ds1 <- interp c1
  ds2 <- interp c2
  Leaf (union ds1 ds2)
interp (Observe p) = Leaf p
interp (Assign x a) = Leaf [[CBin Eq (AVar x) a]]
interp (Seq c1 c2) = do
  ds1 <- interp c1
  ds2 <- interp c2
  Leaf [union d1 d2 | d1 <- ds1, d2 <- ds2]
  
importance :: Fractional r => Tree r a -> Tree r a
importance (Leaf a) = Leaf a
importance (Scale r t) | is_never (importance t) = Never
importance (Scale r t) | otherwise = Scale r $ importance t
importance (Split t1 t2) | is_never (importance t1) && is_never (importance t2) = Never
importance (Split t1 t2) | is_never (importance t1) = Scale (1/2) $ importance t2
importance (Split t1 t2) | is_never (importance t2) = Scale (1/2) $ importance t1
importance (Split t1 t2) | otherwise = Split (importance t1) (importance t2)
importance (Corec f) | is_never (importance (f (Corec f))) = Never
importance (Corec f) | otherwise = importance (f (Corec f))
importance Never = Never

infer :: Fractional r => Obs Pred r -> Com -> Sampler (Maybe r)
infer f c bits = sample f (importance $ reduce $ interp c) bits

run :: Floating r => Obs Pred r -> Com -> Int -> IO ([r], r, r, r, (r, r))
run f c n = do
  g <- newStdGen
  let bits = randoms g :: [Bool]
  let sampler = infer f c
  let (msamples, remaining_bits) = sample_many sampler (\bits -> ([], bits)) n bits
  let samples = catMaybes msamples
  let m = fromIntegral $ length samples
  let mqhat = foldl (+) 0.0 samples / m
  let sqhat = foldl (\b a -> b + (a - mqhat)*(a - mqhat)) 0.0 samples / m
  let bound = (2.58*sqhat)/(sqrt m)
  let confidence = (mqhat - bound, mqhat + bound)
  return (samples, mqhat, m, bound, confidence)

com1 :: Com
com1 =
  Seq
  (Flip
   (Assign "x" (AVal (VFloat 3)))
   (Flip
    (Assign "x" (AVal (VFloat 4)))
    (Assign "x" (AVal (VFloat 5)))))
  (Observe [[CBin Lt (AVal (VFloat 3)) (AVar "x")]])

ex1 = run (fst . get "x") com1 

com2 :: Com
com2 =
  ite (CBin Eq (AVar "x") (AVal (VFloat 3)))
    (Observe [[CBin Lt (AVal (VFloat 2)) (AVar "x")]])
    (Observe [[CBin Eq (AVar "x") (AVal (VFloat 3))]]) 
  
com3 :: Com
com3 =
  let cx = Flip (Assign "x" (AVal (VFloat 0))) (Assign "x" (AVal (VFloat 1))) in
  let cy = Flip (Assign "y" (AVal (VFloat 0))) (Assign "y" (AVal (VFloat 1))) in
  Seq cx (Seq cy (Observe [[CBin Lt (AVar "x") (AVal (VFloat 1.1))]]))   

ex3 = run (fst . get "x") (Flip (Assign "x" (AVal (VFloat 0))) (Assign "x" (AVal (VFloat 1))))

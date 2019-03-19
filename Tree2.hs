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
data Constraint = CEq Atom Atom | CLt Atom Atom deriving (Show, Eq)
type Pred = [[Constraint]] -- DNF

instance Ord Atom where
  compare (AVar x) (AVar y) = compare x y
  compare (AVal _) (AVar _) = LT
  compare (AVar _) (AVal _) = GT
  compare (AVal v1) (AVal v2) = compare v1 v2

instance Ord Constraint where
  compare (CEq _ _) (CLt _ _) = LT
  compare (CEq a1 a2) (CEq b1 b2) =
    case compare a1 b1 of
      EQ -> compare a2 b2
      _ -> compare a1 b1
  compare (CLt a1 a2) (CLt b1 b2) =
    case compare a1 b1 of
      EQ -> compare a2 b2
      _ -> compare a1 b1

subst :: Name -> Val -> Constraint -> Constraint
subst x v (CEq a1 a2) = CEq (asubst x v a1) (asubst x v a2)
subst x v (CLt a1 a2) = CLt (asubst x v a1) (asubst x v a2)

asubst :: Name -> Val -> Atom -> Atom
asubst x v (AVar y) = if x==y then AVal v else AVar y
asubst x v (AVal vy) = AVal vy

solve :: Pred -> [[(Name, Val)]]
solve cs = mapMaybe (go []) (map sort cs)
  where go :: [(Name, Val)] -> [Constraint] -> Maybe [(Name, Val)]
        go binds [] = Just binds

        -- Ground constraints:
        go binds (CEq (AVal vx) (AVal vy) : rest) = if vx==vy then go binds rest else Nothing
        go binds (CLt (AVal vx) (AVal vy) : rest) = if vx<vy then go binds rest else Nothing

        -- Equality constraints:
        go binds (CEq (AVar x) (AVal v) : rest) = go ((x, v) : binds) (map (subst x v) rest)

        -- These constraints should not occur in well-typed programs
        -- (because variables will have been substituted by prior sorted constraints):
        go binds (CEq (AVal _) (AVar _) : _) = Nothing                
        go binds (CEq (AVar _) (AVar _) : _) = Nothing        
        go binds (CLt (AVal _) (AVar _) : _) = Nothing
        go binds (CLt (AVar _) (AVal _) : _) = Nothing

reduce :: Tree r Pred -> Tree r Pred
reduce = bind (\p -> case solve p of
                [] -> Never
                (_ : _) -> Leaf p)

mget :: Name -> Pred -> Maybe Val
mget x p = do
  case solve p of
    [] -> Nothing
    (m : []) -> lookup x m
    _ : _ -> Nothing

get :: Name -> Pred -> Val
get x p =
  case mget x p of
    Nothing -> error $ "name " ++ x ++ " not bound"
    Just v -> v
  
data Com =
    Flip Com Com
  | Observe Pred
  | Assign Name Atom
  | Seq Com Com  
--  | Ite Atom Com Com
--  | While Exp Com

interp :: Num r => Com -> Tree r Pred
interp (Flip c1 c2) = Split (interp c1) (interp c2)
interp (Observe p) = Leaf p
interp (Assign x a) = Leaf [[CEq (AVar x) a]]
interp (Seq c1 c2) = do
  ds1 <- interp c1
  ds2 <- interp c2
  Leaf [union d1 d2 | d1 <- ds1, d2 <- ds2]
--interp (Ite a c1 c2) = do
--  p1 <- interp c1
--  p2 <- interp c2
--  Leaf [CImpl a 
  
importance :: Fractional r => Tree r a -> Tree r a
importance (Leaf a) = Leaf a
importance (Scale r t) = Scale r $ importance t
importance (Split Never Never) = Never
importance (Split Never t2) = Scale (1/2) $ importance t2
importance (Split t1 Never) = Scale (1/2) $ importance t1
importance (Split t1 t2) = Split (importance t1) (importance t2)
importance (Corec f) = importance (f (Corec f))
importance Never = Never

infer :: Fractional r => Obs Pred r -> Com -> Sampler (Maybe r)
infer f c bits = sample f (importance $ reduce $ interp c) bits

run :: Floating r => Obs Pred r -> Com -> Int -> IO (r, r, (r, r))
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
  return (m, bound, confidence)

com1 :: Com
com1 =
  Seq
  (Flip
   (Assign "x" (AVal (VFloat 3)))
   (Flip
    (Assign "x" (AVal (VFloat 4)))
    (Assign "x" (AVal (VFloat 5)))))
  (Observe [[CLt (AVal (VFloat 3)) (AVar "x")]])

com2 :: Com
com2 =
  Seq (
    (Assign "x" (AVal (VFloat 4)))
    )
  (Observe [[CLt (AVal (VFloat 3)) (AVar "x")]])

ex1 = run (\st -> get "x" st) com1 
  

{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Tree2 where

import Data.List (union, intersectBy, sort)
import Data.Maybe (catMaybes, mapMaybe)
import System.Random

data Tree r a =
    Leaf a
  | Split (Tree r a) (Tree r a)
  | Corec (Tree r a -> Tree r a)
  | Never
  | Scale r (Tree r a)

is_never :: Tree r a -> Bool
is_never Never = True
is_never _ = False

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
sample f (Split t1 _) (False : bits) = sample f (Scale (1/2) t1) bits
sample f (Split _ t2) (True : bits)  = sample f (Scale (1/2) t2) bits
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
  | ELt Exp Exp

einterp :: Exp -> St -> Val
einterp (EVal v) _ = v
einterp (EVar x) st = get x st
einterp (ELt e1 e2) st =
  case (einterp e1 st, einterp e2 st) of
    (VFloat r1, VFloat r2) -> VBool (r1 < r2)
    (_, _) -> error "ill-typed expression"

is_true :: Exp -> St -> Bool
is_true e st =
  case einterp e st of
    VBool b -> b
    _ -> error "not a Boolean"

data Com =
    Flip Com Com
  | Observe Exp
  | Assign Name Exp
  | Seq Com Com  
  | Ite Exp Com Com

interp :: Com -> Tree r St -> Tree r St
interp (Flip c1 c2) t = bind (\st -> Split (interp c1 (Leaf st)) (interp c2 (Leaf st))) t
interp (Observe e) t = bind (\st -> if is_true e st then Leaf st else Never) t
interp (Assign x e) t = bind (\st -> Leaf $ upd x (einterp e st) st) t
interp (Seq c1 c2) t = interp c2 (interp c1 t)
interp (Ite e c1 c2) t = bind (\st -> if is_true e st then interp c1 (Leaf st) else interp c2 (Leaf st)) t

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

infer :: Fractional r => Obs St r -> Com -> Tree r St -> Sampler (Maybe r)
infer f c t bits = sample f (opt $ interp c t) bits

run :: Floating r => Obs St r -> Com -> Int -> IO (r, (r, r))
run f c n = do
  g <- newStdGen
  let bits = randoms g :: [Bool]
  let sampler = infer f c (Leaf empty)
  let (msamples, remaining_bits) = sample_many sampler (\bits -> ([], bits)) n bits
  let samples = catMaybes msamples
  let m = fromIntegral $ length samples
  let mqhat = foldl (+) 0.0 samples / m
  let sqhat = foldl (\b a -> b + (a - mqhat)*(a - mqhat)) 0.0 samples / m
  let bound = (2.58*sqhat)/(sqrt m)
  let confidence = (mqhat - bound, mqhat + bound)
  return (bound, confidence)

com1 :: Com
com1 =
  Seq
  (Flip
   (Assign "x" (EVal (VFloat 3)))
   (Flip
    (Assign "x" (EVal (VFloat 4)))
    (Assign "x" (EVal (VFloat 5)))))
  (Observe (ELt (EVal (VFloat 3)) (EVar "x")))

ex1 = run (\st -> get "x" st) com1 
  

module Tree2 where

import Data.Maybe (catMaybes)
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

bind :: (a -> Tree r b) -> Tree r a -> Tree r b
bind g (Leaf a) = g a
bind g (Scale r t) = Scale r (bind g t)
bind g (Split t1 t2) = Split (bind g t1) (bind g t2)
bind g (Corec f) = bind g (f (Corec f))
bind g Never = Never

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
    deriving (Show)

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
interp (Flip c1 c2) t = Split (interp c1 t) (interp c2 t)
interp (Observe e) t = bind (\st -> if is_true e st then Leaf st else Never) t
interp (Assign x e) t = bind (\st -> Leaf $ upd x (einterp e st) st) t
interp (Seq c1 c2) t = interp c2 (interp c1 t)
interp (Ite e c1 c2) t = bind (\st -> if is_true e st then interp c1 (Leaf st) else interp c2 (Leaf st)) t

importance :: Fractional r => Tree r St -> Tree r St
importance (Leaf a) = Leaf a
importance (Scale r t) = Scale r $ importance t
importance (Split Never t2) = Scale (1/2) $ importance t2
importance (Split t1 Never) = Scale (1/2) $ importance t1
importance (Split t1 t2) = Split (importance t1) (importance t2)
importance (Corec f) = importance (f (Corec f))

infer :: Fractional r => Obs St r -> Com -> Tree r St -> Sampler (Maybe r)
infer f c t bits = sample f (importance $ interp c t) bits

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
  

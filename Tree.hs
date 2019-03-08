{-# LANGUAGE DeriveFunctor #-}
module Tree where

import System.Random
import Control.Monad.State

data Tree a =
    Leaf a
  | Node (Tree a) (Tree a)
    deriving (Show)


type Sampler a = [Bool] -> (a, [Bool])

sample_many :: Sampler a -> Sampler [a] -> Int -> Sampler [a]
sample_many sampler acc 0 = acc
sample_many sampler acc n | n > 0 =
  sample_many sampler
    (\bits -> let (a, rest1) = sampler bits in
              let (as, rest2) = acc rest1 in
              (a : as, rest2)) (n-1)

sample_tree :: Tree a -> Sampler a
sample_tree (Leaf a) bits = (a, bits)
sample_tree (Node t1 t2) (False : bits) = sample_tree t1 bits
sample_tree (Node t1 t2) (True : bits) = sample_tree t2 bits
sample_tree (Node _ _) [] = error "not enough bits"

data Event = A | B | C deriving (Show, Eq)

twothirds_onethird :: Tree Event
twothirds_onethird = go False
  where go :: Bool -> Tree Event
        go False  = Node (Leaf A) (go True)
        go True = Node (Leaf B) (go False)

data Context a =
    Hole
  | L (Context a) (Tree a)
  | R (Tree a) (Context a)
    deriving (Show)    

data Dir = DLeft | DRight | DUp | DHere

type Zipper a = (Context a, Tree a)

move :: Dir -> Zipper a -> Zipper a
move DLeft (ctx, Leaf a) = (ctx, Leaf a)
move DLeft (ctx, Node t1 t2) = (L ctx t2, t1)
move DRight (ctx, Leaf a) = (ctx, Leaf a)
move DRight (ctx, Node t1 t2) = (R t1 ctx, t2)
move DUp (L ctx t2, t1) = (ctx, Node t1 t2)
move DUp (R t1 ctx, t2) = (ctx, Node t1 t2)
move DUp (Hole, t) = (Hole, t)
move DHere z = z

fill :: Zipper a -> Tree a
fill (Hole, t) = t
fill (L ctx t2, t) = Node (fill (ctx, t)) t2
fill (R t1 ctx, t) = Node t1 (fill (ctx, t))

depth :: Context a -> Int
depth Hole = 0
depth (L ctx t2) = 1 + depth ctx
depth (R t1 ctx) = 1 + depth ctx

weight :: (Eq a, Fractional r) => Tree a -> a -> r
weight (Leaf b) a | a==b = 1
weight (Leaf b) a | a/=b = 0
weight (Node t1 t2) a    = 1/2*weight t1 a + 1/2*weight t2 a

cweight :: (Eq a, Fractional r) => Context a -> a -> r
cweight Hole _ = 0
cweight (L ctx t2) a = 1/2*cweight ctx a + 1/2*weight t2 a
cweight (R t1 ctx) a = 1/2*weight t1 a + 1/2*cweight ctx a

data Prog a =
    Stop
  | Upd (Tree a -> Tree a) (Prog a) {-Update the focused tree-}
  | Move Dir (Prog a)               {-Move the focus-}

data EvalState a r = EvalState {
  cur_zipper :: Zipper a,
  cur_cweight :: a -> r,
  cur_depth :: Int
}

get_zipper :: State (EvalState a r) (Zipper a)
get_zipper = get >>= \s -> return $ cur_zipper s

get_cweight :: State (EvalState a r) (a -> r)
get_cweight = get >>= \s -> return $ cur_cweight s

get_depth :: State (EvalState a r) Int
get_depth = get >>= \s -> return $ cur_depth s

eval :: (Show a, Eq a, Floating r) => Prog a -> (a -> r) -> State (EvalState a r) (Sampler r)
eval Stop f = do
  z <- get_zipper
  return $ \bits ->
    let (a, rest) = sample_tree (fill z) bits
    in (f a, rest)
eval (Upd delt p) f = do
  z <- get_zipper
  cw <- get_cweight
  d <- get_depth
  let (ctx, t) = z
  let new_t = delt t
  let new_f x = (1 + (b - c)/(a*2**fromIntegral d + c)) * f x
        where a = cw x
              b = weight t x
              c = weight new_t x
  eval p new_f
eval (Move dir p) f = do
  z <- get_zipper
  let (new_ctx, new_t) = move dir z
  modify (\_ -> EvalState (new_ctx, new_t) (cweight new_ctx) (depth new_ctx))
  eval p f
        
run :: (Show a, Eq a, Floating r) => Prog a -> Zipper a -> (a -> r) -> Int -> IO (r, r)
run p z f n = do
  let (ctx, t) = z
  let sampler = evalState (eval p f) (EvalState z (cweight ctx) (depth ctx))
  g <- newStdGen
  let bits = randoms g :: [Bool]
  let (samples, remaining_bits) = sample_many sampler (\bits -> ([], bits)) n bits
  let mqhat = foldl (+) 0.0 samples / (fromIntegral $ length samples)
  let sqhat = foldl (\b a -> b + (a - mqhat)*(a - mqhat)) 0.0 samples
              / (fromIntegral $ length samples)
  let bound = (2.58*sqhat)/(sqrt 8)              
  let confidence = (mqhat - bound, mqhat + bound)
  return confidence

p = Node (Leaf B) (Node (Leaf A) (Leaf B))

rv A = 10.0
rv B = 1.0

--prog7 = Stop
prog7 = Move DLeft (Upd (\_ -> Leaf A) Stop)
-- This version of prog7 overweights A:
--prog7 = [(\t -> t, DLeft), (\_ -> Leaf A, DUp), (\t -> t, DRight), (\t -> t, DRight),
--         (\t -> Node (Leaf A) (Leaf B), DHere)]
-- This version of prog7 underweights A:
--prog7 = []
example7 = run prog7 (Hole, p) rv 100


module Tree where

import System.Random

data Tree a =
    Leaf a
  | Node (Tree a) (Tree a)
    deriving (Show)


type Sampler a = [Bool] -> (a, [Bool])

sample_many :: Sampler a -> [a] -> Int -> Sampler [a]
sample_many sampler acc 0 = \bits -> (acc, bits)
sample_many sampler acc n | n > 0 =
  \bits -> let (a, rest) = sampler bits in sample_many sampler (a : acc) (n-1) rest

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

example1 = fill (L Hole (Leaf B), Leaf A)

weight :: (Eq a, Fractional r) => a -> Tree a -> r
weight a (Leaf b) | a==b = 1
weight a (Leaf b) | a/=b = 0
weight a (Node t1 t2)    = 1/2*weight a t1 + 1/2*weight a t2

example2 = weight A (Node (Leaf A) (Leaf B))
example3 = weight A (Node (Leaf A) (Node (Leaf A) (Leaf B)))
example4 = weight B (Node (Leaf A) (Node (Leaf A) (Leaf B)))

cweight :: (Eq a, Fractional r) => a -> Context a -> r
cweight _ Hole = 0
cweight a (L ctx t2) = 1/2*cweight a ctx + 1/2*weight a t2
cweight a (R t1 ctx) = 1/2*weight a t1 + 1/2*cweight a ctx

example5 = cweight A (L Hole (Leaf B))
example6 = cweight A (L Hole (Leaf A))

type Delta a = Tree a -> (Tree a, Dir)

reweight :: (Eq a, Floating r) => Delta a -> Zipper a -> a -> r
reweight delt (ctx, t) x = (b - c)/(a*2**d + c) + 1 {-= (a + 2**(-d)*b)/(a + 2**(-d)*c)-}
  where a = cweight x ctx
        b = weight x t
        (new_t, _) = delt t
        c = weight x new_t
        d = fromIntegral $ depth ctx

type Program a = [Delta a]

eval :: (Eq a, Floating r) => Program a -> Zipper a -> (a -> r) -> Sampler r
eval [] z f = \bits -> let (a, rest) = sample_tree (fill z) bits in (f a, rest)
eval (delt : rest) (ctx, t) f = eval rest new_z new_f
  where new_f = \x -> reweight delt (ctx, t) x * f x
        (new_t, dir) = delt t
        new_z = move dir (ctx, new_t)
        
run :: (Eq a, Floating r) => Program a -> Zipper a -> (a -> r) -> Int -> IO (r, r)
run p z f n = do
  let sampler = eval p z f
  g <- newStdGen
  let bits = randoms g :: [Bool]
  let (samples, remaining_bits) = sample_many sampler [] n bits
  let mqhat = foldl (+) 0.0 samples / (fromIntegral $ length samples)
  let sqhat = foldl (\b a -> b + (a - mqhat)*(a - mqhat)) 0.0 samples
              / (fromIntegral $ length samples)
  let bound = (2.58*sqhat)/(sqrt 8)              
  let confidence = (mqhat - bound, mqhat + bound)
  return confidence

p = Node (Leaf B) (Node (Leaf A) (Leaf B))

rv A = 10.0
rv B = 1.0

prog7 = [(\t -> (t, DLeft)), (\_ -> (Leaf A, DUp))]         
-- This version of prog7 overweights A:
--prog7 = [(\t -> t, DLeft), (\_ -> Leaf A, DUp), (\t -> t, DRight), (\t -> t, DRight),
--         (\t -> Node (Leaf A) (Leaf B), DHere)]
-- This version of prog7 underweights A:
--prog7 = []
example7 = run prog7 (Hole, p) rv 1000

        


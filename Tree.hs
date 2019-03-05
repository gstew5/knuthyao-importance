module Tree where

data Tree a =
    Leaf a
  | Node (Tree a) (Tree a)
    deriving (Show)

sample :: [Bool] -> Tree a -> a
sample _ (Leaf a) = a
sample (False : bits) (Node t1 t2) = sample bits t1
sample (True : bits)  (Node t1 t2) = sample bits t2

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

type Delta a = Tree a -> Tree a

reweight :: (Eq a, Floating r) => Delta a -> Zipper a -> a -> r
reweight delt (ctx, t) x = (b - c)/(a*2**d + c) + 1 {-= (a + 2**(-d)*b)/(a + 2**(-d)*c)-}
  where a = cweight x ctx
        b = weight x t
        c = weight x (delt t)
        d = fromIntegral $ depth ctx

type Program a = [(Delta a, Dir)]

run :: (Eq a, Floating r) => Program a -> Zipper a -> (a -> r) -> ([Bool] -> r)
run [] z f = \bits -> f $ sample bits (fill z)
run ((delt, dir) : rest) (ctx, t) f = run rest new_z new_f
  where new_f = \x -> reweight delt (ctx, t) x * f x
        new_z = move dir (ctx, delt t)
        
p = Node (Leaf B) (Node (Leaf A) (Leaf B))

rv A = 10.0
rv B = 1.0

--example8 = run [(\t -> t, DLeft), (\_ -> Leaf A, DUp), (\t -> t, DRight), (\t -> t, DRight), (\t -> Node (Leaf A) (Leaf B), DHere)] (Hole, p) rv
example8 = run [(\t -> t, DLeft), (\_ -> Leaf A, DUp)] (Hole, p) rv
--example8 = run [] (Hole, p) rv

s0 = example8 [False, False, True]
s1 = example8 [False, True, True]
s2 = example8 [True, False, True]
s3 = example8 [True, True, True]
s4 = example8 [False, False, False]
s5 = example8 [False, True, False]
s6 = example8 [True, False, False]
s7 = example8 [True, True, False]

samples = [s0, s1, s2, s3, s4, s5, s6, s7]

mqhat = foldl (+) 0.0 samples / (fromIntegral $ length samples)

sqhat = foldl (\b a -> b + (a - mqhat)*(a - mqhat)) 0.0 samples
        / (fromIntegral $ length samples)

confidence = (mqhat - bound, mqhat + bound)
  where bound = (2.58*sqhat)/(sqrt 8)

        


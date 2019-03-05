module Tree where

data Tree a =
    Leaf a
  | Node (Tree a) (Tree a)
    deriving (Show)

sample :: [Bool] -> Tree a -> a
sample _ (Leaf a) = a
sample (False : bits) (Node t1 t2) = sample bits t1
sample (True : bits)  (Node t1 t2) = sample bits t2

data Event = A | B deriving (Show, Eq)

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

data Dir = DownLeft | DownRight | Up | Here

type Zipper a = (Context a, Tree a)

move :: Dir -> Zipper a -> Zipper a
move DownLeft (ctx, Leaf a) = (ctx, Leaf a)
move DownLeft (ctx, Node t1 t2) = (L ctx t2, t1)
move DownRight (ctx, Leaf a) = (ctx, Leaf a)
move DownRight (ctx, Node t1 t2) = (R t1 ctx, t2)
move Up (L ctx t2, t1) = (ctx, Node t1 t2)
move Up (R t1 ctx, t2) = (ctx, Node t1 t2)
move Up (Hole, t) = (Hole, t)
move Here z = z

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
reweight delt (ctx, t) x = (a + 2**(-d)*b)/(a + 2**(-d)*c)
  where a = cweight x ctx
        b = weight x t
        c = weight x (delt t)
        d = fromIntegral $ depth ctx

type Program a = [(Delta a, Dir)]

exec :: (Eq a, Floating r) => Program a -> Zipper a -> (a -> r) -> ([Bool] -> r)
exec [] z f = \bits -> f $ sample bits (fill z)
exec ((delt, dir) : rest) (ctx, t) f = exec rest new_z new_f
  where new_f = \x -> reweight delt (ctx, t) x * f x
        new_z = move dir (ctx, delt t)
        
unif = Node (Leaf A) (Leaf B)

rv A = 1.0
rv B = 1.0

example8 = exec [(\t -> Node t (Leaf B), Here)] (Hole, unif) rv [False, True]


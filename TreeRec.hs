{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE DeriveFoldable, DeriveFunctor, RankNTypes, TupleSections #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}

-- | KY trees in open recursion style. It seems less convenient in a
-- couple ways (e.g., no regular functor or monad instances, plus it's
-- just weird), but gives an interesting way to construct infinite
-- trees from coalgebras.

module Main where

import Control.Monad.State
import Data.Functor.Product
import Data.Maybe (fromJust)
import Data.Tuple (swap)
import System.Random

-- Fixed point of a functor.
newtype Fix f = Fix { unFix :: f (Fix f) }

-- The tree functor.
data TreeF a b =
  Leaf a
  | Split b b
  | Never
  deriving (Functor, Show)

-- Take the fixed point. In Hask, the least fixed point and greatest
-- fixed point are the same (I think because the least fixed point
-- must include infinite trees due to lazy semantics), So Tree is both
-- the initial TreeF-algebra and final TreeF-coalgebra.
type Tree a = Fix (TreeF a)

-- Fix a payload type A. The tree functor:
-- F(X) = A + X*X + 1

-- A TreeF-algebra is a type Y and a function [alg : A + Y*Y + 1 -> Y].

-- For any such algebra, there exists a unique homomorphism from Tree
-- to Y, [cata : Tree -> Y] (because Tree is the initial
-- TreeF-algebra), which is the tree recursor specialized to that
-- algebra.

-- E.g., let Y = Int and
-- alg a = 1
-- alg (y1, y2) = y1 + y2
-- alg tt = 0
-- Then the induced [cata : Tree -> Int] is the tree size function
-- (giving size 0 to Never).


-- A TreeF-coalgebra is a type Y and a function [coalg : Y -> A + Y*Y + 1].

-- For any such coalgebra, there exists a unique anamorphism
-- [ana : Y -> Tree], a tree generator from seed of type Y (because
-- Tree is the final TreeF-coalgebra).

-- E.g., Y = ? (TODO: how to define the construction of a tree from a
-- pmf / table as a coalgebra?)

instance Show a => Show (Tree a) where
  show (Fix Never) = "Never"
  show (Fix t) = "(" ++ show t ++ ")"

toSexp :: Show a => Tree a -> String
toSexp = cata alg
  where
    alg (Leaf x) = show x
    alg (Split s1 s2) = "(" ++ s1 ++ " " ++ s2 ++ ")"
    alg Never = "Never"

mkLeaf :: a -> Tree a
mkLeaf = Fix . Leaf

mkSplit :: Tree a -> Tree a -> Tree a
mkSplit t1 t2 = Fix $ Split t1 t2

mkNever :: Tree a
mkNever = Fix Never


-- General setup for algebras/coalgebras and cata-/anamorphisms.
type Algebra f a = f a -> a
type Coalgebra f a = a -> f a

cata :: Functor f => Algebra f b -> Fix f -> b
cata alg = alg . fmap (cata alg) . unFix

ana :: Functor f => Coalgebra f b -> b -> Fix f
ana coalg = Fix . fmap (ana coalg) . coalg

-- A hylomorphism is an anamorphism followed by a catamorphism. For
-- example, when the functor is NatF or ListF, hylomorphisms
-- correspond to computations whose call stack resembles a list (first
-- build up the stack, then collapse it down to accumulate a result).
hylo :: Functor f => Algebra f b -> Coalgebra f a -> a -> b
hylo alg coalg = cata alg . ana coalg

-- Special case for trees.
type TreeAlgebra a b = Algebra (TreeF a) b
type TreeCoalgebra a b = Coalgebra (TreeF a) b

-- Old cata and ana definitions specialized to trees.
-- cata :: TreeAlgebra a b -> Tree a -> b
-- cata alg t = case unFix t of
--   Leaf x -> alg $ Leaf x
--   Split t1 t2 -> alg $ Split (cata alg t1) (cata alg t2)
--   Never -> alg Never

-- ana :: TreeCoalgebra a b -> b -> Tree a
-- ana coalg y = case coalg y of
--   Leaf x -> mkLeaf x
--   Split y1 y2 -> mkSplit (ana coalg y1) (ana coalg y2)
--   Never -> mkNever

-- The open recursion style is equivalent to the regular one.
data Tree' a =
  Leaf' a
  | Split' (Tree' a) (Tree' a)
  | Never'

tree'OfTree :: Tree a -> Tree' a
tree'OfTree = cata alg
  where
    alg :: TreeAlgebra a (Tree' a)
    alg (Leaf x) = Leaf' x
    alg (Split t1 t2) = Split' t1 t2
    alg Never = Never'

treeOfTree' :: Tree' a -> Tree a
treeOfTree' = ana coalg
  where
    coalg :: TreeCoalgebra a (Tree' a)
    coalg (Leaf' x) = Leaf x
    coalg (Split' t1 t2) = Split t1 t2
    coalg Never' = Never


-- Tree size function.
tree_size :: Tree a -> Int
tree_size = cata alg
  where
    alg :: TreeAlgebra a Int
    alg (Leaf _) = 1
    alg (Split n m) = n + m
    alg Never = 0

-- Fair coin tree.
t1 :: Tree Int
t1 = mkSplit (mkLeaf 0) (mkLeaf 1)

-- (2/3, 1/3) infinite KY tree. 'Never' is used as a placeholder for
-- where the rest of the tree is to be generated.
t2 :: Tree Int
t2 = ana coalg mkNever
  where
    coalg :: TreeCoalgebra Int (Tree Int)
    coalg (Fix Never) = Split (mkLeaf 0) (mkSplit (mkLeaf 1) mkNever)
    coalg (Fix t) = t

-- Prefix as a catamorphism.
prefix :: Int -> Tree a -> Tree a
prefix n | n <= 0 = const mkNever
prefix n = cata alg
  where
    alg :: TreeAlgebra a (Tree a)
    alg (Split t1 t2) = mkSplit (prefix (n-1) t1) (prefix (n-1) t2)
    alg t = Fix t

-- Prefix as an anamorphism.
prefix' :: Int -> Tree a -> Tree a
prefix' n | n <= 0 = const mkNever
prefix' n = ana coalg
  where
    coalg :: TreeCoalgebra a (Tree a)
    coalg (Fix (Split t1 t2)) = Split (prefix' (n-1) t1) (prefix' (n-1) t2)
    coalg (Fix t) = t

-- The above definitions are cheating a bit by using explicit
-- recursion inside of the algebra/coalgebra. We can avoid this by
-- doing induction on natural numbers instead.

data NatF a =
  O
  | S a
  deriving (Functor, Show)

type Nat = Fix NatF
type NatAlgebra a = Algebra NatF a
type NatCoalgebra a = Coalgebra NatF a

natOfIntCoalg :: NatCoalgebra Int
natOfIntCoalg n | n <= 0 = O
natOfIntCoalg n = S (n-1)

natOfInt :: Int -> Nat
natOfInt = ana natOfIntCoalg

prefixAlg :: NatAlgebra (Tree a -> Tree a)
prefixAlg O = const mkNever
prefixAlg (S f) = \t -> case t of
  Fix (Split t1 t2) -> mkSplit (f t1) (f t2)
  _ -> t

-- First build up the nat from an int, then collapse it to build the
-- prefix function.
prefix'' :: Int -> Tree a -> Tree a
prefix'' = hylo prefixAlg natOfIntCoalg
  where
    alg :: NatAlgebra (Tree a -> Tree a)
    alg O = const mkNever
    alg (S f) = \t -> case t of
      Fix (Split t1 t2) -> mkSplit (f t1) (f t2)
      _ -> t
    coalg :: NatCoalgebra Int
    coalg n | n <= 0 = O
    coalg n = S (n-1)


-- fmap
treeMap :: (a -> b) -> Tree a -> Tree b
treeMap f = cata alg
  where
    alg (Leaf x) = mkLeaf $ f x
    alg (Split t1 t2) = mkSplit t1 t2
    alg Never = mkNever

-- Monadic join.
μ :: Tree (Tree a) -> Tree a
μ = cata alg
  where
    alg (Leaf t) = t
    alg (Split t1 t2) = mkSplit t1 t2
    alg Never = mkNever

-- Monadic bind.
bind :: Tree a -> (a -> Tree b) -> Tree b
bind t f = μ $ treeMap f t

-- Sequential product.
product_tree :: Tree a -> Tree b -> Tree (a, b)
product_tree t1 t2 = bind t1 $ \x -> treeMap (x,) t2

-- Parallel product (NOT GOOD).
product_tree' :: Tree a -> Tree b -> Tree (a, b)
product_tree' = cata alg
  where
    alg :: TreeAlgebra a (Tree b -> Tree (a, b))
    alg (Leaf x) = treeMap (x,)
    alg Never = const mkNever
    alg (Split f g) = \t ->
      case unFix t of
        Leaf y -> mkSplit (f t) (g t)
        Never -> mkNever
        Split t1 t2 -> mkSplit (f t1) (g t2)

proj1_tree :: Tree (a, b) -> Tree a
proj1_tree = treeMap fst

proj2_tree :: Tree (a, b) -> Tree b
proj2_tree = treeMap snd


-- data ListF a b =
--   Nil
--   | Cons a b
--   deriving (Functor, Show)

-- type List a = Fix (ListF a)
-- type ListAlgebra a b = Algebra (ListF a) b
-- type ListCoalgebra a b = Coalgebra (ListF a) b

-- mkList :: [a] -> List a
-- mkList = ana coalg
--   where
--     coalg :: ListCoalgebra a [a]
--     coalg [] = Nil
--     coalg (x:xs) = Cons x xs


headMaybe :: [a] -> Maybe a
headMaybe [] = Nothing
headMaybe (x:_) = Just x

type Bits = [Bool]
type Sampler = State Bits

sample :: Tree a -> Sampler (Maybe a)
sample = cata alg
  where
    alg :: TreeAlgebra a (Sampler (Maybe a))
    alg (Leaf x) = return $ Just x
    alg (Split s1 s2) = do
      bit <- gets headMaybe
      case bit of
        Just b -> do
          modify tail
          if b then s1 else s2
        Nothing -> error "sample: out of bits"
    alg Never = return Nothing

n_samples :: Tree a -> Int -> Sampler [Maybe a]
n_samples t n = mapM (const $ sample t) [0..n]

run_sampler :: Sampler a -> Bits -> (a, Bits)
run_sampler = runState


main :: IO ()
main = do
  g <- newStdGen
  let bits = randoms g :: [Bool]
  -- let bitList = mkList bits
  -- putStrLn $ show $ prefix'' 5 t1
  -- putStrLn $ show $ prefix'' 5 t2
  let t = product_tree t1 t2
  let t' = product_tree' t1 t2
  -- putStrLn $ show t
  -- putStrLn ""
  -- putStrLn $ show $ prefix'' 5 t'
  -- putStrLn ""
  -- putStrLn $ toSexp $ prefix'' 10 t
  -- putStrLn ""
  -- putStrLn $ toSexp $ prefix'' 10 t'

  -- let t1' = proj1_tree t
  -- let t1'' = proj1_tree t'
  -- putStrLn $ show $ prefix'' 5 t1'
  -- putStrLn $ show $ prefix'' 5 t1''
  -- putStrLn $ toSexp $ prefix'' 10 t1'
  -- putStrLn $ toSexp $ prefix'' 10 t1''
  
  -- let t2' = proj2_tree t
  -- let t2'' = proj2_tree t'
  -- putStrLn $ show $ prefix'' 5 t2'
  -- putStrLn $ show $ prefix'' 5 t2''
  -- putStrLn $ toSexp $ prefix'' 10 t2'
  -- putStrLn $ toSexp $ prefix'' 10 t2''

  let (samples, bits') = run_sampler (n_samples t 100) bits
  putStrLn $ show $ fromJust <$> samples

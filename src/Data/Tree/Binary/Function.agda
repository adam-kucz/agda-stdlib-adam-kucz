{-# OPTIONS --safe --exact-split --prop  #-}
module Data.Tree.Binary.Function where

open import Data.Tree.Binary.Definition
open import Data.Tree.Binary.Property

open import Universes

map : (f : X → Y)(t : BinaryTree X) → BinaryTree Y
map f (leaf x) = leaf (f x)
map f (l /\ r) = map f l /\ map f r

open import Collection
open import Logic

dmap : (t : BinaryTree X)(f : (x : X)(p : x ∈ t) → Y) → BinaryTree Y
dmap (leaf x) f = leaf (f x (x ∈leaf)) 
dmap (l /\ r) f = dmap l (λ x p → f x (x ∈left p /\ r)) /\
                  dmap r (λ x p → f x (x ∈right l /\ p))

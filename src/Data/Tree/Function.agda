{-# OPTIONS --safe --exact-split  #-}
module Data.Tree.Function where

open import Data.Tree.Definition
open import Data.Tree.Property

open import Universes
open import Data.List as L hiding (map)

map : (f : X → Y)(t : Tree X) → Tree Y
map f (leaf x) = leaf (f x)
map f ◻ = ◻
map f (branch (h L.∷ t)) = branch (cons (map f h) (map f (branch t)))

open import Collection
open import Logic

dmap : (t : Tree X)(f : (x : X)(p : x ∈ t) → Y) → Tree Y
dmap (leaf x) f = leaf (f x (x ∈leaf))
dmap ◻ f = ◻
dmap (branch (h ∷ t)) f =
  branch (cons (dmap h λ x p → f x (x ∈branch (h , (x∈x∷ t , p))))
               (dmap (branch t) λ x p → f x (∈tail h p)))

{-# OPTIONS --safe --exact-split --prop  #-}
module Data.Tree.Definition where

open import Universes
open import Data.List

data Tree (X : 𝒰 ˙) : 𝒰 ˙ where
  leaf : (x : X) → Tree X
  branch : (br : List (Tree X)) → Tree X

infixr 115 _/\_
pattern ◻ = branch []
pattern _/\_ l r = branch [ l ⸴ r ]

cons : (h t : Tree X) → List (Tree X)
cons h (leaf x) = h ∷ [ leaf x ]
cons h (branch br) = h ∷ br

trim : (t : Tree X) → Tree X
trim-list : (l : List (Tree X)) → List (Tree X)

trim (leaf x) = leaf x
trim (branch br) with trim-list br
trim (branch br) | [] = ◻
trim (branch br) | [ h ] = h
trim (branch br) | l@(_ ∷ _ ∷ _) = branch l

cons-if-nonempty : (h : Tree X)(l : List (Tree X)) → List (Tree X)
cons-if-nonempty ◻ l = l
cons-if-nonempty h@(leaf _) l = h ∷ l
cons-if-nonempty h@(branch (_ ∷ _)) l = h ∷ l

trim-list [] = []
trim-list (h ∷ l) = cons-if-nonempty (trim h) (trim-list l)


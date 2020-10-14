{-# OPTIONS --safe --exact-split  #-}
module Data.Tree.Location where

open import Data.Tree.Definition

open import Universes
open import Data.Nat hiding (l)

data Location : 𝒰₀ ˙ where
  leaf : Location
  branch : (n : ℕ)(loc : Location) → Location

open import Type.Sum hiding (_,_)
open import Data.List hiding (_!_)
open import Collection hiding (_++_)

shift : Location → Location
shift leaf = leaf
shift (branch n x) = branch (n +1) x

locations : (t : Tree X) → List Location
locations (leaf x) = [ leaf ]
locations ◻ = []
locations (branch (h ∷ br)) =
  map (branch 0) (locations h) ++ map shift (locations (branch br))

open import Logic
open import Proof

leaf∉locations-branch :
  (br : List (Tree X))
  → ---------------------------
  leaf ∉ locations (branch br)
leaf∉locations-branch (h ∷ br) p
  with ⟶ (∈++ (map (branch 0) (locations h))
               (map shift (locations (branch br)))) p
leaf∉locations-branch (h ∷ br) p | ∨left q
  with ∈map⁻¹ (locations h) (branch 0) q
leaf∉locations-branch (h ∷ br) p | ∨left q | _ , ()
leaf∉locations-branch (h ∷ br) p | ∨right q
  with ∈map⁻¹ (locations (branch br)) shift q
leaf∉locations-branch (h ∷ br) p | ∨right q | leaf , (_ , p') =
  leaf∉locations-branch br p'

open import Data.Maybe

_!_ : (t : Tree X)(loc : Location) → Maybe X
◻ ! _ = nothing
leaf x ! leaf = just x
leaf _ ! branch _ _ = nothing
branch (h ∷ br) ! leaf = nothing
branch (h ∷ br) ! branch 0 loc = h ! loc
branch (h ∷ br) ! branch (n +1) loc = branch br ! branch n loc

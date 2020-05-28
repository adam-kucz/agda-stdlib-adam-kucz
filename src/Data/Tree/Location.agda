{-# OPTIONS --safe --exact-split --prop  #-}
module Data.Tree.Location where

open import Data.Tree.Definition

open import Universes
open import Data.Nat hiding (l)

data Location : 𝒰₀ ˙ where
  leaf : Location
  branch : (n : ℕ)(loc : Location) → Location

open import Type.Sum hiding (_,_)
open import Data.List hiding (_!_[_])
open import Collection hiding (_++_)

shift : Location → Location
shift leaf = leaf
shift (branch n x) = branch (n +1) x

locations : (t : Tree X) → List Location
locations (leaf x) = [ leaf ]
locations ◻ = []
locations (branch (h ∷ br)) =
  map (branch 0) (locations h) ++ map shift (locations (branch br))

open import Proposition.Empty renaming (⊥-recursion to ⊥ₜ-recursion)
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

_!_[_] : (t : Tree X)(loc : Location)(p : loc ∈ locations t) → X
leaf x ! _ [ p ] = x
branch br ! leaf [ p ] = ⊥ₜ-recursion _ (leaf∉locations-branch br p)
branch (h ∷ br) ! branch zero loc [ p ] = h ! loc [ p' p ]
  where p' : (p : branch 0 loc ∈ locations (branch (h ∷ br)))
             → --------------------------------------------------
             loc ∈ locations h
        p' p with ⟶ (∈++ (map (branch 0) (locations h))
                          (map shift (locations (branch br)))) p
        p' p | ∨left q with ∈map⁻¹ (locations h) (branch 0) q
        p' p | ∨left q | loc , (Id-refl _ , q') = q'
        p' p | ∨right q with ∈map⁻¹ (locations (branch br)) shift q
        p' p | ∨right q | leaf , ()
        p' p | ∨right q | branch _ _ , ()
branch (h ∷ br) ! branch (n +1) loc [ p ] = branch br ! branch n loc [ p' p ]
  where p' : (p : branch (n +1) loc ∈ locations (branch (h ∷ br)))
             → --------------------------------------------------
             branch n loc ∈ locations (branch br)
        p' p with ⟶ (∈++ (map (branch 0) (locations h))
                          (map shift (locations (branch br)))) p
        p' p | ∨left q with ∈map⁻¹ (locations h) (branch 0) q
        p' p | ∨left q | _ , ()
        p' p | ∨right q with ∈map⁻¹ (locations (branch br)) shift q
        p' p | ∨right q | branch _ _ , (Id-refl _ , q') = q'

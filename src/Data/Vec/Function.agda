{-# OPTIONS --safe --exact-split --prop  #-}
module Data.Vec.Function where

open import Data.Vec.Definition
open import Data.Vec.Property

open import Universes
open import Data.List

to-vec : (l : List X) → Vec X (len l)
to-vec [] = []
to-vec (h ∷ l) = h ∷ to-vec l

open import Proposition.Identity
open import Proposition.Empty
open import Proposition.Decidable
open import Data.Nat
open import Collection

vec-remove :
  (x : X)
  (v : Vec X (m +1))
  (p : x ∈ v)
  ⦃ dec== : HasDecidableIdentity X ⦄
  → --------------------
  Vec X m
vec-remove x (h ∷ v) p with decide (h == x)
vec-remove x (h ∷ v) p | true _ = v
vec-remove {m = zero} x (h ∷ v) p | false ¬p =
  ⊥-recursion (Vec _ 0) (contradiction p)
  where contradiction : (p : x ∈ h ∷ v) → ⊥
        contradiction (x∈x∷ t) = ¬p (refl x)
vec-remove {m = m +1} x (h ∷ v) p | false ¬p =
  h ∷ vec-remove x v (p' p)
  where p' : (p : x ∈ h ∷ v) → x ∈ v
        p' (x∈x∷ t) = ⊥-recursionₚ (x ∈ v) (¬p (refl x))
        p' (x∈tail h p) = p

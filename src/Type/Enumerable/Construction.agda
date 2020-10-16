{-# OPTIONS --exact-split --safe --prop #-}
module Type.Enumerable.Construction where

open import Type.Enumerable.Definition

open import Universes
open import Proposition.Identity
open import Proposition.Sum
open import Collection
open import Data.List hiding (_++_)

is-singleton : (X : 𝒰 ˙) → 𝒰 ˙
is-singleton X = Σₚ λ (c : X) → ∀ (x : X) → c == x

singleton-is-enumerable : is-singleton X → is-enumerable X
singleton-is-enumerable (c , p) = [ c ] , all-are-in-[c]
  where all-are-in-[c] : ∀ x → x ∈ [ c ]
        all-are-in-[c] x with Id.refl c ← p x = x∈x∷ []

open import Type.Empty
open import Type.Unit

𝟘-is-enumerable : is-enumerable 𝟘
𝟘-is-enumerable = [] , λ ()

𝟙-is-enumerable : is-enumerable 𝟙
𝟙-is-enumerable = [ ⋆ ] , λ { ⋆ → x∈x∷ []}

open import Type.BinarySum
open import Logic
open import Proof

binary-sum-preserves-enumerability :
  (p : is-enumerable X)
  (q : is-enumerable Y)
  → --------------------------------------------------
  is-enumerable (X + Y)
binary-sum-preserves-enumerability (lx , ∀x∈lx) (ly , ∀y∈ly) =
  lx' ++ ly' ,
  λ { (inl x) → ⟵ (++-prop {l' = ly'}) $ ∨left (∈map inl $ ∀x∈lx x)
    ; (inr y) → ⟵ (++-prop {l = lx'}) $ ∨right (∈map inr $ ∀y∈ly y)}
  where lx' = map inl lx
        ly' = map inr ly

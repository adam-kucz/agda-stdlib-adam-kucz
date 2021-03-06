{-# OPTIONS --exact-split --exact-split --safe --prop #-}
module Type.Finite where

open import PropUniverses
open import Data.List
open import Data.Vec
open import Collection
open import Logic

contains-all :
  (X : 𝒰 ˙)
  {Col : 𝒱 ˙}
  (l : Col)
  ⦃ col : Collection 𝒲 Col X ⦄
  → ------------------------
  𝒰 ⊔ 𝒲 ᵖ
contains-all X l = ∀ (x : X) → x ∈ l

is-finite : (X : 𝒰 ˙) → 𝒰 ᵖ
is-finite X = ∃ λ (l : List X) → contains-all X l
  

open import Proposition.Sum

Finite : (𝒰 : Universe) → 𝒰 ⁺ ˙
Finite 𝒰 = Σₚ λ (X : 𝒰 ˙) → is-finite X

{-
open import Data.Nat
open import Proposition.Decidable

card :
  (Fin : Finite 𝒰)
  ⦃ dec : HasDecidableIdentity X ⦄ →
  let X = elem Fin in
  ∃ λ n →
  ∃ λ (v : Vec X n) →
    contains-all X v ∧
    (∀ m (p : m < n) → ¬ ∃ λ (v' : Vec X m) → contains-all X v')
card (X , (l , p)) = {!!}
-}

{-# OPTIONS --exact-split --safe #-}
module Type.Finite.Definition where

open import Universes
open import Data.List renaming ([_] to L[_])
open import Collection
open import Logic

contains-all :
  (X : 𝒰 ˙)
  {Col : 𝒱 ˙}
  (l : Col)
  ⦃ col : Collection 𝒲 Col X ⦄
  → ------------------------
  𝒰 ⊔ 𝒲 ˙
contains-all X l = ∀ (x : X) → x ∈ l

is-infinite is-finite : (X : 𝒰 ˙) → 𝒰 ˙
is-infinite X = ¬ ∃ λ (l : List X) → contains-all X l
is-finite X = ¬ is-infinite X

open import Type.Sum

Finite : (𝒰 : Universe) → 𝒰 ⁺ ˙
Finite 𝒰 = Σ is-finite

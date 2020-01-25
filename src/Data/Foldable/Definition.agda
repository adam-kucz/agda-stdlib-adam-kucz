{-# OPTIONS --exact-split --safe --prop #-}
module Data.Foldable.Definition where

open import Universes

open import Structure.Monoid
open import Data.Nat hiding (_⊔_)

record Foldable (F : (X : 𝒰 ˙) → 𝒱 ˙) : 𝒰ω where
  field
    fold-map :
      {Y : 𝒲 ˙}⦃ mon : Monoid Y ⦄ 
      (f : (x : X) → Y)
      (fx : F X)
      → ------------------
      Y

  length : (fx : F X) → ℕ
  length = fold-map ⦃ Monoid+ ⦄ (λ _ → 1)
  
open Foldable ⦃ … ⦄ public

open import Function

fold :
  {F : 𝒰 ˙ → 𝒱 ˙}
  ⦃ f : Foldable F ⦄
  ⦃ m : Monoid X ⦄
  → --------------------
  (fx : F X) → X
fold = fold-map id


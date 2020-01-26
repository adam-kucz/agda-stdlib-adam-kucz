{-# OPTIONS --exact-split --prop --safe #-}
module Data.Bool.Correspondence where

open import Data.Bool.Definition

open import PropUniverses
open import Proposition.Decidable as Dec hiding (true; false)

to-bool :
  (𝑋 : 𝒰 ᵖ)
  ⦃ dec : Decidable 𝑋 ⦄
  → ------------------
  Bool
to-bool 𝑋 with decide 𝑋
to-bool _ | Dec.true _ = true
to-bool _ | Dec.false _ = false

open import Proposition.Identity
open import Logic

_<~>_ : (𝑋 : 𝒰 ᵖ)(b : Bool) → 𝒰 ᵖ
𝑋 <~> b = ∃ λ (d : Decidable 𝑋) → to-bool 𝑋 ⦃ d ⦄ == b

_<~~>_ : (𝐴 : 𝒰 ᵖ → 𝒱 ᵖ)(f : Bool → Bool) → 𝒰 ⁺ ⊔ 𝒱 ᵖ
_<~~>_ {𝒰 = 𝒰} 𝐴 f = ∀ (𝑋 : 𝒰 ᵖ)(b : Bool)(p : 𝑋 <~> b) → 𝐴 𝑋 <~> f b

_<~2~>_ : 
  (𝐴 : 𝒰 ᵖ → 𝒱 ᵖ → 𝒲 ᵖ)
  (f : (b₀ b₁ : Bool) → Bool)
  → ------------------------
  𝒰 ⁺ ⊔ 𝒱 ⁺ ⊔ 𝒲 ᵖ
_<~2~>_ {𝒰 = 𝒰} 𝐴 f = ∀ (𝑋 : 𝒰 ᵖ)(b : Bool)(p : 𝑋 <~> b) → 𝐴 𝑋 <~~> f b

⊥<~>false : ⊥ <~> false
⊥<~>false = Dec.false (λ ()) , refl false

⊤<~>true : ⊤ <~> true
⊤<~>true = Dec.true ⋆ₚ , refl true

¬<~>not : (¬_ {𝒰}) <~~> not
¬<~>not 𝑋 true (Dec.true p₁ , refl true) = Dec.false (λ ¬p₁ → ¬p₁ p₁) , refl false
¬<~>not 𝑋 false (Dec.false ¬p₁ , refl false) = Dec.true ¬p₁ , refl true

∧<~>and : (_∧_ {𝒰}{𝒱}) <~2~> _and_
∧<~>and 𝑋 true (Dec.true p₂ , refl true) 𝑋₁ true (Dec.true p₁ , refl true) =
  Dec.true (p₂ , p₁) , refl true
∧<~>and 𝑋 true (Dec.true p₂ , refl true) 𝑋₁ false (Dec.false ¬p , refl false) =
  Dec.false (λ z → ¬p (∧right z)) , refl false
∧<~>and 𝑋 false (Dec.false ¬p , refl false) 𝑋₁ b d =
  Dec.false (λ z → ¬p (∧left z)) , refl false

∨<~>or : (_∨_ {𝒰}{𝒱}) <~2~> _or_
∨<~>or 𝑋 true (Dec.true p₂ , refl true) 𝑋₁ b d = Dec.true (∨left p₂) , refl true
∨<~>or 𝑋 false (Dec.false ¬p , refl false) 𝑋₁ true (Dec.true p₁ , refl true) =
  Dec.true (∨right p₁) , refl true
∨<~>or 𝑋 false (Dec.false ¬p , refl false) 𝑋₁ false (Dec.false ¬p₁ , refl false) =
  Dec.false (λ { (∨left p) → ¬p p ; (∨right q) → ¬p₁ q}) , refl false

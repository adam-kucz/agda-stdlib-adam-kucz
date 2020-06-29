{-# OPTIONS --exact-split --safe --prop #-}
open import Universes
open import Relation.Binary.Definition

module Proposition.Sum.Property {R₀ : BinRel 𝒰 X}{R₁ : BinRel 𝒱 X} where

open import Proposition.Sum.Definition

open import Relation.Binary.Property

instance
  Reflexive∧ :
    ⦃ refl-R₀ : Reflexive R₀ ⦄
    ⦃ refl-R₁ : Reflexive R₁ ⦄
    → --------------------------
    Reflexive (λ x y → R₀ x y ∧ R₁ x y)
  Symmetric∧ :
    ⦃ refl-R₀ : Symmetric R₀ ⦄
    ⦃ refl-R₁ : Symmetric R₁ ⦄
    → --------------------------
    Symmetric (λ x y → R₀ x y ∧ R₁ x y)
  Transitive∧ :
    ⦃ refl-R₀ : Transitive R₀ ⦄
    ⦃ refl-R₁ : Transitive R₁ ⦄
    → --------------------------
    Transitive (λ x y → R₀ x y ∧ R₁ x y)

refl ⦃ Reflexive∧ ⦄ x = refl x , refl x
sym ⦃ Symmetric∧ ⦄ (p , q) = sym p , sym q
trans ⦃ Transitive∧ ⦄ (p , q) (p' , q') = trans p p' , trans q q'

{-# OPTIONS --exact-split --safe --prop #-}
module Function.Property where

open import PropUniverses
open import Proposition.Identity using (_==_; refl)
open import Proposition.Sum
open import Logic
open import Function.Basic
open import Function.Equivalence

record Involutive {X : 𝒰 ˙} (f : (x : X) → X) : 𝒰 ᵖ where
  field
    invol : ∀ x → f (f x) == x

open Involutive ⦃ ... ⦄ public

record Injective {X : 𝒰 ˙} {A : (x : X) → 𝒱 ˙} (f : (x : X) → A x) : 𝒰 ⊔ 𝒱 ᵖ where
  field
    inj : ∀ {x y} (p : f x == f y) → x == y

open Injective ⦃ ... ⦄ public

invertible : {X : 𝒰 ˙} {Y : 𝒱 ˙} (f : (x : X) → Y) → 𝒰 ⊔ 𝒱 ᵖ
invertible f = ∃ λ g → g ∘ f ~ id ∧ f ∘ g ~ id
  where open import Proposition.Sum using (∃; _∧_)

record Surjective {X : 𝒰 ˙} {Y : 𝒱 ˙} (f : (x : X) → Y) : 𝒰 ⊔ 𝒱 ᵖ where
  field
    sur : ∀ (y : Y) → ∃ λ x → f x == y

open Surjective ⦃ ... ⦄ public

record Bijective {X : 𝒰 ˙} {Y : 𝒱 ˙} (f : (x : X) → Y) : 𝒰 ⊔ 𝒱 ᵖ where
  field
    ⦃ injective ⦄ : Injective f
    ⦃ surjective ⦄ : Surjective f

open Bijective ⦃ … ⦄ public

Bijection : (X : 𝒰 ˙) (Y : 𝒱 ˙) →  𝒰 ⊔ 𝒱 ˙
Bijection X Y = Σₚ λ (f : (x : X) → Y) → Bijective f

instance
  DefaultBijection : {f : (x : X) → Y}
    ⦃ _ : Injective f ⦄
    ⦃ _ : Surjective f ⦄
    → -------------------
    Bijective f
  DefaultBijection = record {}

instance
  Injective-id : Injective (𝑖𝑑 X)
  inj ⦃ Injective-id ⦄ (refl x) = refl x

  Surjective-id : Surjective (𝑖𝑑 X)
  sur ⦃ Surjective-id ⦄ y = y , refl y


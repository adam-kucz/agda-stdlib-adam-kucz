{-# OPTIONS --exact-split --safe --prop #-}
module Function.Property where

open import PropUniverses
open import Prop'.Identity
  renaming (Idₚ to Id) using (_==_)
open import Prop'.Sum
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
  where open import Prop'.Sum using (∃; _∧_)

record Surjective {X : 𝒰 ˙} {A : (x : X) → 𝒱 ˙} (f : (x : X) → A x) : 𝒰 ⊔ 𝒱 ᵖ where
  field
    sur : ∀ {x} (y : A x) → ∃ λ x → f x == y

open Surjective ⦃ ... ⦄ public

record Bijective {X : 𝒰 ˙} {A : (x : X) → 𝒱 ˙} (f : (x : X) → A x) : 𝒰 ⊔ 𝒱 ᵖ where
  field
    ⦃ injective ⦄ : Injective f
    ⦃ surjective ⦄ : Surjective f

open Bijective ⦃ … ⦄ public

Bijection : (X : 𝒰 ˙) (A : (x : X) → 𝒱 ˙) →  𝒰 ⊔ 𝒱 ˙
Bijection X A = Σₚ λ (f : (x : X) → A x) → Bijective f

instance
  DefaultBijection : {f : (x : X) → Y}
    ⦃ _ : Injective f ⦄
    ⦃ _ : Surjective f ⦄
    → -------------------
    Bijective f
  DefaultBijection = record {}

open import Proof
open import Function.Proof
open import Relation.Binary

invertible-is-bijective : {f : (x : X) → Y} → invertible f ↔ Bijective f
⟶ (invertible-is-bijective {f = f}) (g , (g∘f~id , f∘g~id)) = record {}
  where
    instance
      Injective-f : Injective f
      inj ⦃ Injective-f ⦄ {x} {y} fx==fy =
        proof x
          〉 _==_ 〉 g (f x) :by: sym (g∘f~id x)
          〉 _==_ 〉 g (f y) :by: ap g fx==fy
          〉 _==_ 〉 y       :by: g∘f~id y
        qed
      Surjective-f : Surjective f
      sur ⦃ Surjective-f ⦄ y = g y , f∘g~id y
⟵ (invertible-is-bijective {X = X} {Y = Y}) q = inverse , {!!}
  where instance _ = q
        inverse : (y : Y) → X
        inverse y with sur ⦃ Bijective.surjective q ⦄ y
        inverse _ | x = {!!}

instance
  Injective-id : Injective (𝑖𝑑 X)
  inj ⦃ Injective-id ⦄ (Id.refl x) = refl x

  Surjective-id : Surjective (𝑖𝑑 X)
  sur ⦃ Surjective-id ⦄ y = y , refl y


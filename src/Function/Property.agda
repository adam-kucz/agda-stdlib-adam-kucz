{-# OPTIONS --exact-split --safe --prop #-}
module Function.Property where

open import PropUniverses
open import Proposition.Identity using (_==_; refl)
open import Proposition.Sum
open import Logic
open import Function.Basic hiding (_$_)
open import Function.Equivalence

record Involutive {X : 𝒰 ˙} (f : (x : X) → X) : 𝒰 ᵖ where
  field
    invol : f ∘ f ~ id

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

instance
  DefaultBijective : {f : (x : X) → Y}
    ⦃ _ : Injective f ⦄
    ⦃ _ : Surjective f ⦄
    → -------------------
    Bijective f
  DefaultBijective = record {}

record Bijection (X : 𝒰 ˙) (Y : 𝒱 ˙) : 𝒰 ⊔ 𝒱 ˙ where
  field
    forw : (x : X) → Y
    back : (y : Y) → X
    left-inverse : back ∘ forw ~ 𝑖𝑑 X
    right-inverse : forw ∘ back ~ 𝑖𝑑 Y

open Bijection ⦃ … ⦄ public

{-# DISPLAY Bijection.forw B = forw #-}
{-# DISPLAY Bijection.back B = back #-}

invertible-is-bijective : ∀ {f : (x : X) → Y} (p : invertible f) → Bijective f
invertible-is-bijective {f = f} (g , (g∘f~id , f∘g~id)) = DefaultBijective
  where open import Proof
        instance
          Surjective-f : Surjective f
          sur ⦃ Surjective-f ⦄ y = g y , f∘g~id y
          Injective-f : Injective f
          inj ⦃ Injective-f ⦄ {x} {y} p =
            proof x
              〉 _==_ 〉 g (f x) :by: sym $ g∘f~id x
              〉 _==_ 〉 g (f y) :by: ap g p
              〉 _==_ 〉 y       :by: g∘f~id y
            qed

bijection-is-bijective : (b : Bijection X Y)
  → let instance _ = b in
  Bijective forw ∧ Bijective back
bijection-is-bijective b =
  invertible-is-bijective (back , (left-inverse , right-inverse)) ,
  invertible-is-bijective (forw , (right-inverse , left-inverse))
  where instance _ = b

involutive-is-bijection :
  {f : (x : X) → X}
  (p : Involutive f)
  → -----------------------
  Bijection X X
involutive-is-bijection {f = f} p = record
  {forw = f; back = f; left-inverse = invol; right-inverse = invol}
  where instance _ = p

instance
  Injective-id : Injective (𝑖𝑑 X)
  inj ⦃ Injective-id ⦄ (refl x) = refl x

  Surjective-id : Surjective (𝑖𝑑 X)
  sur ⦃ Surjective-id ⦄ y = y , refl y



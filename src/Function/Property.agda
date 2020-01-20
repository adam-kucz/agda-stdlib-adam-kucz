{-# OPTIONS --exact-split --safe --prop #-}
module Function.Property where

open import PropUniverses
open import Proposition.Identity renaming (Idₚ to Id) using (_==_)
open import Proposition.Sum
open import Logic
open import Function.Basic hiding (_$_)
open import Function.Equivalence

record LeftInverse {X : 𝒰 ˙}{Y : 𝒱 ˙}
    (f : X → Y)
    (f⁻¹ : Y → X)
    : --------------
    𝒰 ⊔ 𝒱 ᵖ
    where
  field
     left-inv : f⁻¹ ∘ f ~ id

open LeftInverse ⦃ ... ⦄ public

left-inverse-of :
  (f : X → Y)
  {f⁻¹ : Y → X}
  ⦃ r : LeftInverse f f⁻¹ ⦄
  → ----------------------------
  f⁻¹ ∘ f ~ id
left-inverse-of _ = left-inv

record RightInverse {X : 𝒰 ˙}{Y : 𝒱 ˙}
    (f : X → Y)
    (f⁻¹ : Y → X)
    : --------------
    𝒰 ⊔ 𝒱 ᵖ
    where
  field
     right-inv : f ∘ f⁻¹ ~ id

open RightInverse ⦃ ... ⦄ public

right-inverse-of :
  (f : X → Y)
  {f⁻¹ : Y → X}
  ⦃ r : RightInverse f f⁻¹ ⦄
  → ----------------------------
  f ∘ f⁻¹ ~ id
right-inverse-of _ = right-inv

record Inverse {X : 𝒰 ˙}{Y : 𝒱 ˙}
    (f : X → Y)
    (f⁻¹ : Y → X)
    : --------------
    𝒰 ⊔ 𝒱 ᵖ
    where
  field
     ⦃ inverse-left ⦄ : LeftInverse f f⁻¹
     ⦃ inverse-right ⦄ : RightInverse f f⁻¹

open Inverse ⦃ … ⦄ public

record Invertible {X : 𝒰 ˙}{Y : 𝒱 ˙}(f : X → Y) : 𝒰 ⊔ 𝒱 ˙ where
  field
    inv : Y → X
    ⦃ inverse ⦄ : Inverse f inv

_⁻¹ : {X : 𝒰 ˙}{Y : 𝒱 ˙}
  (f : X → Y)
  ⦃ i : Invertible f ⦄
  → -----------------------
  (y : Y) → X
_⁻¹ f ⦃ i ⦄ = Invertible.inv i

instance
  DefaultInverse : {f : X → Y}{f⁻¹ : Y → X}
    ⦃ _ : LeftInverse f f⁻¹ ⦄
    ⦃ _ : RightInverse f f⁻¹ ⦄
    → ------------------------
    Inverse f f⁻¹
  DefaultInverse = record {}

record Injective {X : 𝒰 ˙} {A : (x : X) → 𝒱 ˙} (f : (x : X) → A x) : 𝒰 ⊔ 𝒱 ᵖ where
  field
    inj : ∀ {x y} (p : f x == f y) → x == y

open Injective ⦃ ... ⦄ public

record Surjective {X : 𝒰 ˙} {Y : 𝒱 ˙} (f : (x : X) → Y) : 𝒰 ⊔ 𝒱 ᵖ where
  field
    surj : ∀ (y : Y) → ∃ λ x → f x == y

open Surjective ⦃ … ⦄ public

sur :
  (f : X → Y)
  (y : Y)
  ⦃ s : Surjective f ⦄
  → ∃ λ x → f x == y
sur _ y = surj y

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
    ⦃ bi-inverse ⦄ : Inverse forw back

open Bijection ⦃ … ⦄ public

{-# DISPLAY Bijection.forw B = forw #-}
{-# DISPLAY Bijection.back B = back #-}

open import Proof

bijection-is-bijective : (b : Bijection X Y)
  → let instance _ = b in
  Bijective forw ∧ Bijective back
bijection-is-bijective b = record {} , record {}
  where instance
          _ = b
          Surjective-forw : Surjective (forw ⦃ b ⦄)
          Surjective-back : Surjective (back ⦃ b ⦄)
          Injective-forw : Injective (forw ⦃ b ⦄)
          Injective-back : Injective (back ⦃ b ⦄)
        surj ⦃ Surjective-forw ⦄ y = back y , right-inv y
        surj ⦃ Surjective-back ⦄ x = forw x , left-inv x
        inj ⦃ Injective-forw ⦄ {x}{y} p =
          proof x
            〉 _==_ 〉 back (forw x) :by: sym $ left-inv x
            〉 _==_ 〉 back (forw y) :by: ap back p
            〉 _==_ 〉 y             :by: left-inv y
          qed
        inj ⦃ Injective-back ⦄ {x}{y} p =
          proof x
            〉 _==_ 〉 forw (back x) :by: sym $ right-inv x
            〉 _==_ 〉 forw (back y) :by: ap forw p
            〉 _==_ 〉 y             :by: right-inv y
          qed

LeftInverse-id : LeftInverse (𝑖𝑑 X) (𝑖𝑑 X)
left-inv ⦃ LeftInverse-id ⦄ x = refl x

RightInverse-id : RightInverse (𝑖𝑑 X) (𝑖𝑑 X)
right-inv ⦃ RightInverse-id ⦄ x = refl x

Injective-id : Injective (𝑖𝑑 X)
inj ⦃ Injective-id ⦄ (Id.refl x) = refl x

Surjective-id : Surjective (𝑖𝑑 X)
surj ⦃ Surjective-id ⦄ y = y , refl y

Involutive : {X : 𝒰 ˙}(f : X → X) → 𝒰 ᵖ
Involutive f = Inverse f f

mk-involutive : {f : X → X}
  (p : f ∘ f ~ id)
  → -------------------------
  Involutive f
mk-involutive {f = f} p = record {}
  where instance
          lft : LeftInverse f f
          rght : RightInverse f f
        left-inv ⦃ lft ⦄ = p
        right-inv ⦃ rght ⦄ = p

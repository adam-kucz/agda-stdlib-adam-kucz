{-# OPTIONS --exact-split --safe --prop #-}
module Function.Property where

open import PropUniverses
open import Proposition.Identity.Definition
import Proposition.Identity.Heterogeneous as Het
open import Proposition.Sum
open import Logic.Basic
open import Function.Basic hiding (_$_)
open import Function.Equivalence.Definition

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
    inj : ∀ {x y} (p : f x Het.== f y) → x == y

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

Injective-id : Injective (𝑖𝑑 X)
inj ⦃ Injective-id ⦄ (Het.refl x) = refl x

Surjective-id : Surjective (𝑖𝑑 X)
surj ⦃ Surjective-id ⦄ y = y , refl y

Involutive : {X : 𝒰 ˙}(f : X → X) → 𝒰 ᵖ
Involutive f = Inverse f f

module mkInvolutive {f : X → X}(p : f ∘ f ~ id) where
  instance
    lft : LeftInverse f f
    rght : RightInverse f f
  left-inv ⦃ lft ⦄ = p
  right-inv ⦃ rght ⦄ = p

module IdInvolutive {𝒰}{X : 𝒰 ˙} where
  open mkInvolutive {X = X}{f = id} Het.refl

record Idempotent {X : 𝒰 ˙}(f : (x : X) → X) : 𝒰 ᵖ where
  field
    idemp : ∀ x → f (f x) == f x 

open Idempotent ⦃ … ⦄ public

open import Data.Nat.Definition
open import Data.Nat.Syntax
open Pattern

injective-repeat :
  (f : X → X)
  (m : ℕ)
  ⦃ injective : Injective f ⦄
  → ---------------------------
  Injective (repeat f m)

inj ⦃ injective-repeat f 0 ⦄ = het==→==
inj ⦃ injective-repeat f (m +1) ⦃ injective ⦄ ⦄ p =
  inj ⦃ injective-repeat f m ⦄ (==→het== (inj ⦃ injective ⦄ p))

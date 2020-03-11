{-# OPTIONS --exact-split --safe --prop #-}
module Relation.Binary.Property where

open import PropUniverses
open import Relation.Binary.Definition
open import Proposition.Identity.Definition using (_==_; _≠_)
open import Logic

private
  module RelProp (property : RelProperty) where
    record Property {X : 𝒰 ˙} (R : BinRel 𝒱 X) : 𝒰 ⊔ 𝒱 ᵖ where
      field
        prop-name : property R

    open Property ⦃ … ⦄ public

open RelProp (λ _R_ → ∀ {x y z} (p : x R y) (q : y R z) → x R z)
  renaming (Property to Transitive; prop-name to trans) public
open RelProp (λ _R_ → ∀ x → x R x)
  renaming (Property to Reflexive; prop-name to refl) public
open RelProp (λ _R_ → ∀ x → ¬ x R x)
  renaming (Property to Irreflexive; prop-name to irrefl) public
open RelProp (λ _R_ → ∀ {x y} (p : x R y) → y R x)
  renaming (Property to Symmetric; prop-name to sym) public
open RelProp (λ _R_ → ∀ {x y} (p : x R y) (q : y R x) → x == y)
  renaming (Property to Antisymmetric; prop-name to antisym) public
open RelProp (λ _R_ → ∀ {x y} (p : x R y) → ¬ y R x)
  renaming (Property to Asymmetric; prop-name to asym) public
open RelProp (λ _R_ → ∀ x y → x R y ∨ y R x)
  renaming (Property to Connex; prop-name to total) public
open RelProp (λ _R_ → ∀ {x y} (p : x ≠ y) → x R y ∨ y R x)
  renaming (Property to Semiconnex; prop-name to semicon) public
open RelProp (λ _R_ → ∀ {x y} (p : x R y) → x R x) public
  renaming (Property to LeftQuasiReflexive; prop-name to left-quasirefl)
open RelProp (λ _R_ → ∀ {x y} (p : x R y) → y R y) public
  renaming (Property to RightQuasiReflexive; prop-name to right-quasirefl)

instance
  DefaultSemiconnex :
    {R : BinRel 𝒰 X}
    ⦃ _ : Connex R ⦄
    → -------------------------
    Semiconnex R
  semicon ⦃ DefaultSemiconnex ⦄ {x} {y} _ = total x y

record Equivalence {X : 𝒱 ˙} (R : BinRel 𝒰 X) : 𝒰 ⊔ 𝒱 ᵖ where
  field
    ⦃ equiv-reflexive ⦄ : Reflexive R
    ⦃ equiv-symmetric ⦄ : Symmetric R
    ⦃ equiv-transitive ⦄ : Transitive R

open Equivalence ⦃ … ⦄ public

record QuasiReflexive {X : 𝒱 ˙} (R : BinRel 𝒰 X) : 𝒰 ⊔ 𝒱 ᵖ where
  field
    ⦃ qr-left ⦄ : LeftQuasiReflexive R
    ⦃ qr-right ⦄ : RightQuasiReflexive R

open QuasiReflexive ⦃ … ⦄ public

instance
  DefaultEquivalence :
    {R : BinRel 𝒰 X}
    ⦃ _ : Reflexive R ⦄
    ⦃ _ : Symmetric R ⦄
    ⦃ _ : Transitive R ⦄
    → -------------------------
    Equivalence R
  DefaultQuasiReflexive :
    {R : BinRel 𝒰 X}
    ⦃ _ : LeftQuasiReflexive R ⦄
    ⦃ _ : RightQuasiReflexive R ⦄
    → -------------------------
    QuasiReflexive R

DefaultEquivalence = record {}
DefaultQuasiReflexive = record {}

total-other :
  {_R_ : BinRel 𝒰 X}
  ⦃ _ : Connex _R_ ⦄
  {x y : X}
  (p : ¬ x R y)
  → -------------------
  y R x
total-other {x = x}{y} p with total x y
total-other {_R_ = _R_}{x = x} {y} p | ∨left q =
  ⊥-recursion (y R x) (p q)
total-other {x = x} {y} p | ∨right q = q

record Minimal {X : 𝒰 ˙} (_≼_ : BinRel 𝒱 X) (⊥ : X) : 𝒰 ⊔ 𝒱 ᵖ where
  field
    minimality : ∀ {x} (p : x ≼ ⊥) → x == ⊥

open Minimal ⦃ … ⦄ public

open import Proposition.Decidable.Definition using (Decidable)

infix 21 _⊆_
record _⊆_ {X : 𝒰 ˙} {Y : 𝒱 ˙} (_R_ : Rel 𝒲 X Y) (_P_ : Rel 𝒯 X Y) : 𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯 ᵖ
  where
  field
    subrel : ∀ {x} {y} (xRy : x R y) → x P y

open _⊆_ ⦃ … ⦄ public

instance
  Reflexive⊆ : Reflexive (_⊆_ {𝒲 = 𝒰}{X = X}{Y})
  Transitive⊆ : Transitive (_⊆_ {𝒲 = 𝒰}{X = X}{Y})

open import Proposition.Function using (_$_; _∘_; id)

subrel ⦃ refl ⦃ Reflexive⊆ ⦄ R ⦄ = id
subrel ⦃ trans ⦃ Transitive⊆ ⦄ P⊆Q Q⊆R ⦄ = subrel ∘ subrel
  where instance
          _ = P⊆Q
          _ = Q⊆R

infix 19 _~_
record _~_ {X : 𝒰 ˙} {Y : 𝒱 ˙} (R : Rel 𝒲 X Y) (P : Rel 𝒯 X Y) : 𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯 ᵖ
  where
  field
    ⦃ ~-⊆ ⦄ : R ⊆ P
    ⦃ ~-⊇ ⦄ : P ⊆ R

open _~_ ⦃ … ⦄ public

instance
  Default-~ : {R : Rel 𝒰 X Y}{P : Rel 𝒱 X Y}
    ⦃ R⊆P : R ⊆ P ⦄
    ⦃ P⊆R : P ⊆ R ⦄
    → --------------
    R ~ P
Default-~ = record {}

open import Logic

↔-→-⊆ :
  {_R_ : Rel 𝒰 X Y}
  {_P_ : Rel 𝒱 X Y}
  (equiv : ∀ {x y} → x R y ↔ x P y)
  → --------------------------------
  _R_ ⊆ _P_
↔-→-⊇ :
  {_R_ : Rel 𝒰 X Y}
  {_P_ : Rel 𝒱 X Y}
  (equiv : ∀ {x y} → x R y ↔ x P y)
  → --------------------------------
  _P_ ⊆ _R_

subrel ⦃ ↔-→-⊆ equiv ⦄ = ⟶ equiv
subrel ⦃ ↔-→-⊇ equiv ⦄ = ⟵ equiv

instance
  Reflexive~ : Reflexive (_~_ {𝒲 = 𝒰}{X = X}{Y})
  Symmetric~ : Symmetric (_~_ {𝒲 = 𝒰}{X = X}{Y})
  Transitive~ : Transitive (_~_ {𝒲 = 𝒰}{X = X}{Y})

refl ⦃ Reflexive~ ⦄ R = record {}
  where instance _ = refl ⦃ Reflexive⊆ ⦄ R
sym ⦃ Symmetric~ ⦄ P~R = record {}
trans ⦃ Transitive~ ⦄ {P}{Q}{R} P~Q Q~R = record {}
  where instance _ = P~Q; _ = Q~R; P⊆R : P ⊆ R; R⊆P : R ⊆ P
        P⊆R = trans (_~_.~-⊆ P~Q) (_~_.~-⊆ Q~R)
        R⊆P = trans (_~_.~-⊇ Q~R) (_~_.~-⊇ P~Q)

instance
  Irreflexive¬Reflexive :
    {_R_ : BinRel 𝒰 X}
    ⦃ reflexive : Reflexive _R_ ⦄
    → -----------------------------
    Irreflexive (λ x y → ¬ x R y)
  Symmetric¬Symmetric :
    {_R_ : BinRel 𝒰 X}
    ⦃ symmetric : Symmetric _R_ ⦄
    → -----------------------------
    Symmetric (λ x y → ¬ x R y)

irrefl ⦃ Irreflexive¬Reflexive ⦄ x ¬xRx = ¬xRx $ refl x
sym ⦃ Symmetric¬Symmetric ⦄ ¬xRy yRx = ¬xRy $ sym yRx

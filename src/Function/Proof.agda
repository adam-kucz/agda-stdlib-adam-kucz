{-# OPTIONS --exact-split --safe --prop #-}
module Function.Proof where

open import PropUniverses
open import Proposition.Identity.Definition
open import Logic.Basic
open import Relation.Binary.Definition

record Relating {X : 𝒰 ˙} {A : (x : X) → 𝒱 ˙}
    (f : (x : X) → A x)
    (r : BinRel 𝒲 X)
    (r' : {x y : X} → Rel 𝒯 (A x) (A y))
    : --------------------
    𝒰 ⊔ 𝒲 ⊔ 𝒯 ᵖ
    where
  field
    rel-preserv :
      {a b : X}
      (rab : r a b)
      → --------------
      r' (f a) (f b)

open Relating ⦃ ... ⦄ public

ap :
  (f : (x : X) → A x)
  {r : BinRel 𝒰 X}
  {r' : ∀ {a b} → Rel 𝒱 (A a) (A b)}
  ⦃ rel : Relating f r r' ⦄
  {a b : X}
  (rab : r a b)
  → ----------------
  r' (f a) (f b)
ap f = rel-preserv

record Relating-2 {X : 𝒰 ˙}{Y : 𝒱 ˙}{K : (x : X)(y : Y) → 𝒲 ˙}
    (f : (x : X)(y : Y) → K x y)
    (r : BinRel 𝒳 X)
    (r' : BinRel 𝒴 Y)
    (r″ : ∀ {x₀ x₁ y₀ y₁} → Rel 𝒵 (K x₀ y₀) (K x₁ y₁))
    : --------------------
    𝒰 ⊔ 𝒱 ⊔ 𝒳 ⊔ 𝒴 ⊔ 𝒵 ᵖ
    where
  field
    rel-preserv-2 : ∀ {x x' y y'}
      (rxx' : r x x')
      (r'yy' : r' y y')
      → --------------
      r″ (f x y) (f x' y')

open Relating-2 ⦃ … ⦄ public

ap2 : ∀ {K : (x : X)(y : Y) → 𝒰 ˙}
  (f : (x : X)(y : Y) → K x y)
  {r₀ : BinRel 𝒳 X}
  {r₁ : BinRel 𝒴 Y}
  {r₂ : ∀ {x₀ x₁ y₀ y₁} → Rel 𝒵 (K x₀ y₀) (K x₁ y₁)}
  ⦃ rel : Relating-2 f r₀ r₁ r₂ ⦄
  {x₀ x₁ y₀ y₁}
  (r₀x₀x₁ : r₀ x₀ x₁)
  (r₁y₀y₁ : r₁ y₀ y₁)
  → ----------------
  r₂ (f x₀ y₀) (f x₁ y₁)
ap2 f = rel-preserv-2

record UniversalPostfix {X : 𝒰 ˙} {Y : 𝒱 ˙}
    (f : (x : X) → Y)
    (_⊑_ : Rel 𝒲 X Y)
    : --------------------
    𝒰 ⊔ 𝒲 ᵖ where
  field
    postfix : ∀ x → x ⊑ f x

postfix :
  (f : (x : X) → Y)
  {_⊑_ : Rel 𝒲 X Y}
  ⦃ post : UniversalPostfix f _⊑_ ⦄
  (x : X)
  → --------------------------------
  x ⊑ f x
postfix f ⦃ post ⦄ = UniversalPostfix.postfix post

record UniversalPrefix {X : 𝒰 ˙} {Y : 𝒱 ˙}
    (f : (x : X) → Y)
    (_⊑_ : Rel 𝒲 Y X)
    : --------------------
    𝒰 ⊔ 𝒲 ᵖ where
  field
    prefix : ∀ x → f x ⊑ x

prefix :
  (f : (x : X) → Y)
  {_⊑_ : Rel 𝒲 Y X}
  ⦃ post : UniversalPrefix f _⊑_ ⦄
  (x : X)
  → --------------------------------
  f x ⊑ x
prefix f ⦃ pre ⦄ = UniversalPrefix.prefix pre

open import Function.Basic
open import Function.Property
open import Function.Equivalence.Definition

instance
  Relating-all-==-het== : {f : (x : X) → A x} → Relating f _==_ Het._==_
  Relating-all-het== : {f : (x : X) → A x} → Relating f Het._==_ Het._==_
  Relating-2-all-== : {f : X → Y → Z}
    → --------------------------------------
    Relating-2 f _==_ _==_ _==_
  Relating-2-all-het== :
    {K : (x : X)(y : Y) → 𝒰 ˙}
    {f : (x : X)(y : Y) → K x y}
    → ----------------------------
    Relating-2 f Het._==_ Het._==_ Het._==_
  RelatingInjective :
    {f : X → Y}
    ⦃ injective : Injective f ⦄
    → -----------------------------------------------------------
    Relating f (_≠_ {X = X}) (_≠_ {X = Y})
  RelatingInjectiveHet :
    {f : (x : X) → A x}
    ⦃ injective : Injective f ⦄
    → -----------------------------------------------------------
    Relating f (_≠_ {X = X}) (λ {x}{y} → Het._≠_ {X = A x}{Y = A y})
  Relating-∘-~ : {f : (y : Y) → A y} → Relating (f ∘_) (_~_ {X = X}) _~_

open import Proposition.Function renaming (_$_ to _$ₚ_)

rel-preserv ⦃ Relating-all-==-het== {f = f} ⦄
  (refl x) = Het.refl (f x)
rel-preserv ⦃ Relating-all-het== {f = f} ⦄
  (Het.refl x) = Het.refl (f x)
rel-preserv-2 ⦃ Relating-2-all-== {f = f} ⦄
  (refl x) (refl y) = refl (f x y)
rel-preserv-2 ⦃ Relating-2-all-het== {f = f} ⦄
  (Het.refl x) (Het.refl y) = Het.refl (f x y)
Relating.rel-preserv RelatingInjective a≠b fa==fb =
  a≠b $ₚ inj $ₚ ==→het== fa==fb 
Relating.rel-preserv RelatingInjectiveHet a≠b fa==fb =
  a≠b $ₚ inj fa==fb
rel-preserv ⦃ Relating-∘-~ {f = f} ⦄ p x = ap f (p x)

  -- TODO (low priority): think of a different approach, this produces too many choice points
  -- Relating-∧-intro :
  --   {A : Set 𝑙₀}
  --   {B : A → Set 𝑙₁}
  --   {C : A → Set 𝑙₂}
  --   {f : (x : A) → B x}
  --   {r : A → A → Prop 𝑚₀}
  --   {r' : {x y : A} → B x → B y → Prop 𝑚₁}
  --   {r'' : {x y : A} → B x → B y → Prop 𝑚₂}
  --   ⦃ _ : Relating f r r' ⦄
  --   ⦃ _ : Relating f r r'' ⦄
  --   → -----------------------------------
  --   Relating f r (λ a b → r' a b ∧ r'' a b)
  -- rel-preserv ⦃ Relating-∧-intro ⦄ rab = rel-preserv rab , rel-preserv rab

  -- Relating-∧-elim-l :
  --   {A : Set 𝑙₀}
  --   {B : A → Set 𝑙₁}
  --   {C : A → Set 𝑙₂}
  --   {f : (x : A) → B x}
  --   {r : A → A → Prop 𝑚₀}
  --   {r' : A → A → Prop 𝑚₁}
  --   {r'' : {x y : A} → B x → B y → Prop 𝑚₂}
  --   ⦃ _ : Relating f r r'' ⦄
  --   → -----------------------------------
  --   Relating f (λ a b → r a b ∧ r' a b) r''
  -- rel-preserv ⦃ Relating-∧-elim-l ⦄ (left , _) = rel-preserv left

  -- Relating-∧-elim-r :
  --   {A : Set 𝑙₀}
  --   {B : A → Set 𝑙₁}
  --   {C : A → Set 𝑙₂}
  --   {f : (x : A) → B x}
  --   {r : A → A → Prop 𝑚₀}
  --   {r' : A → A → Prop 𝑚₁}
  --   {r'' : {x y : A} → B x → B y → Prop 𝑚₂}
  --   ⦃ _ : Relating f r r'' ⦄
  --   → -----------------------------------
  --   Relating f (λ a b → r' a b ∧ r a b) r''
  -- rel-preserv ⦃ Relating-∧-elim-r ⦄ (_ , right) = rel-preserv right

  -- Relating-∨-intro :
  --   {A : Set 𝑙₀}
  --   {B : A → Set 𝑙₁}
  --   {C : A → Set 𝑙₂}
  --   {f : (x : A) → B x}
  --   {r : A → A → Prop 𝑚₀}
  --   {r' : A → A → Prop 𝑚₁}
  --   {r'' : {x y : A} → B x → B y → Prop 𝑚₂}
  --   ⦃ _ : Relating f r r'' ⦄
  --   ⦃ _ : Relating f r' r'' ⦄
  --   → -----------------------------------
  --   Relating f (λ a b → r a b ∨ r' a b) r''
  -- rel-preserv ⦃ Relating-∨-intro ⦄ (rab ∨∅) = rel-preserv rab
  -- rel-preserv ⦃ Relating-∨-intro ⦄ (∅∨ r'ab) = rel-preserv r'ab

  -- Relating-∨-elim-l :
  --   {A : Set 𝑙₀}
  --   {B : A → Set 𝑙₁}
  --   {C : A → Set 𝑙₂}
  --   {f : (x : A) → B x}
  --   {r : A → A → Prop 𝑚₀}
  --   {r' : {x y : A} → B x → B y → Prop 𝑚₁}
  --   {r'' : {x y : A} → B x → B y → Prop 𝑚₂}
  --   ⦃ _ : Relating f r r' ⦄
  --   → -----------------------------------
  --   Relating f r (λ a b → r' a b ∨ r'' a b)
  -- rel-preserv ⦃ Relating-∨-elim-l ⦄ rab = rel-preserv rab ∨∅

  -- Relating-∨-elim-r :
  --   {A : Set 𝑙₀}
  --   {B : A → Set 𝑙₁}
  --   {C : A → Set 𝑙₂}
  --   {f : (x : A) → B x}
  --   {r : A → A → Prop 𝑚₀}
  --   {r' : {x y : A} → B x → B y → Prop 𝑚₁}
  --   {r'' : {x y : A} → B x → B y → Prop 𝑚₂}
  --   ⦃ _ : Relating f r r' ⦄
  --   → -----------------------------------
  --   Relating f r (λ a b → r'' a b ∨ r' a b)
  -- rel-preserv ⦃ Relating-∨-elim-r ⦄ rab = ∅∨ rel-preserv rab

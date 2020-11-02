{-# OPTIONS --exact-split --prop --safe #-}
module Relation.Binary.Pointwise.Property where

open import Relation.Binary.Pointwise.Definition
open import Relation.Binary
open import Relation.Binary.ReflexiveTransitiveClosure
  renaming (refl-trans-close to rtc)

open import Universes

instance
  Pointwise⊆Pointwise :
    {X : 𝒰 ˙}{A : X → 𝒱 ˙}{B : X → 𝒲 ˙}
    {R : ∀{x x'} → Rel 𝒳 (A x) (B x')}
    {P : ∀{x x'} → Rel 𝒯 (A x) (B x')}
    ⦃ p : ∀ {x}{x'} → R {x}{x'} ⊆ P {x}{x'} ⦄
    → -----------------------------------
    Pointwise {X = X} (λ {x}{x'} → R {x}{x'}) ⊆ Pointwise P

subrel⊆ Pointwise⊆Pointwise xRy x = subrel (xRy x)

{-
open import Type.Finite
open import Proposition.Sum
open import Proposition.Decidable
open import Data.Nat
open import Data.List hiding (last)
open import Data.Vec
open import Collection hiding (_~_)
open import Logic
open import Proof

open import Axiom.FunctionExtensionality

ptwise-rtc-commute :
  {R : BinRel 𝒰 Y}
  ⦃ reflexive : Reflexive R ⦄
  (p : is-finite X)
  ⦃ dec : HasDecidableIdentity X ⦄
  → ------------------------------------------
  Pointwise {X = X} (rtc R) ~ rtc (Pointwise R)
subrel ⦃ ~-⊆ ⦃ ptwise-rtc-commute {Y = Y}{X = X}{R = R} (l , p) ⦄ ⦄ {f} {g} x→f~g = {!!}
  where open import Proposition.Wrapped
        vec-to-f : (v : Vec Y (len l)) → Wrapped (X → Y)
        go :
          {f g : X → Y}
          (l : List (Σₚ λ x →
                     ∃ λ y₀ → 
                     ∃ λ y₁ →
                       y₀ == f x ∧ y₁ == g x ∧ rtc R y₀ y₁))
          (p : contains-all X (map elem l))
          → --------------------
          ∃ λ n → ∃ λ (l : Vec (Vec Y (len l)) (n +1)) → {!vec-to-f!}
        go = {!!}
        vec-to-f v = wrap λ x → v ! index (p x) [ index≤ (p x) ]
--   step (λ x → ⊥-recursion _ $ x ∉∅ $ p x) (rfl g)
-- subrel ⦃ ~-⊆ ⦃ ptwise-rtc-commute (x ∷ l , p) ⦄ ⦄ {f} {g} x→f~g = {!!}
subrel ⦃ ~-⊇ ⦃ ptwise-rtc-commute p ⦄ ⦄ (rfl f) x = rfl (f x)
subrel ⦃ ~-⊇ ⦃ ptwise-rtc-commute p ⦄ ⦄ (step f~g g~*h) x =
  step (f~g x) $ subrel ⦃ ~-⊇ ⦃ ptwise-rtc-commute p ⦄ ⦄ g~*h x
-}

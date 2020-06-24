{-# OPTIONS --exact-split --prop #-}
module Function.BijectionEquivalence where

open import Universes
open import Function.Basic hiding (_$_)
open import Function.Property
open import Proposition.Sum
open import Relation.Binary
open import Logic
open import Proof

open import Axiom.UniqueChoice

bijection-of-bijective :
  (f : X → Y)
  ⦃ b : Bijective f ⦄
  → ---------------
  Bijection X Y
bijection-of-bijective f = record { forw = f; back = inv }
  where uniq : (y : codomain f) → ∃! λ x → f x == y
        uniq y with sur f y
        uniq y | x , p = x , (p , λ x₁ p₁ → inj $ subrel {_R_ = _==_} (
          proof f x₁
            === y   :by: p₁
            === f x :by: sym p
          qed))
        inv : codomain f → domain f
        inv y = elem (!choice (uniq y))
        instance
          RightInverse-f : RightInverse f inv
          LeftInverse-f : LeftInverse f inv
        right-inv ⦃ RightInverse-f ⦄ y =
          subrel $ ∧left $ prop (!choice (uniq y))
        left-inv ⦃ LeftInverse-f ⦄ x =
          subrel $ inj $ subrel $ ∧left $ prop (!choice (uniq (f x)))

{-# OPTIONS --exact-split --prop #-}
module Function.BijectionEquivalence where

open import Universes
open import Function.Basic hiding (_$_)
open import Function.Property
open import Proposition.Sum
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
        uniq y | x , p = x , (p , λ x₁ p₁ → inj (
          proof f x₁
            〉 _==_ 〉 y :by: p₁
            〉 _==_ 〉 f x :by: sym p
          qed))
        inv : codomain f → domain f
        inv y = elem (!choice (uniq y))
        instance
          RightInverse-f : RightInverse f inv
          LeftInverse-f : LeftInverse f inv
        right-inv ⦃ RightInverse-f ⦄ y = ∧left $ prop (!choice (uniq y))
        left-inv ⦃ LeftInverse-f ⦄ x = inj $ ∧left $ prop (!choice (uniq (f x)))

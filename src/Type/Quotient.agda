{-# OPTIONS --exact-split --prop #-}
module Type.Quotient where

open import PropUniverses hiding (Type)
open import Relation.Binary

open import Proposition.Identity hiding (refl)
open import Proposition.Sum
open import Proposition.Function using (_$_)
open import Logic
open import Function hiding (_$_)

open import Axiom.PropositionExtensionality
open import Axiom.FunctionExtensionality

module Quotient (X : 𝒰 ˙) (_≈_ : Rel 𝒱 X X) ⦃ _ : Equivalence _≈_ ⦄ where
  Type : 𝒰 ⊔ 𝒱 ⁺ ˙
  Type = Σₚ λ (c : (x : X) → 𝒱 ᵖ) → ∃ λ x → ∀ x' → c x' == x ≈ x'
  
  class-of : (x : X) → Type
  class-of x = (x ≈_) , (x , λ x' → refl (x ≈ x'))

  class-def : ∀ {x y} (p : class-of x == class-of y) → x ≈ y
  class-def {x} {y} p = sym $ ⟶ (==→↔ $ ==→~ (from-Σₚ== p) x) $ refl x

  eq : ∀ {x y} (p : x ≈ y) → class-of x == class-of y
  eq {x} {y} p = Σₚ== $ fun-ext λ z → prop-ext $ equiv z
    where equiv : ∀ z → x ≈ z ↔ y ≈ z
          ⟶ (equiv z) q = trans (sym p) q
          ⟵ (equiv z) q = trans p q

  elim :
    (𝐴 : (t : Type) → 𝒰 ᵖ)
    (f : (x : X) → 𝐴 (class-of x))
    (t : Type)
    → ----------------------------------------
    𝐴 t
  elim 𝐴 f t@(p , (x , q)) = Id.subst 𝐴 (Id.sym h) (f x)
    where h : t == class-of x
          h = Σₚ== (fun-ext q)

{-# OPTIONS --exact-split --prop #-}
module Function.Property.Unsafe where

open import Function.Property

open import PropUniverses
open import Proposition.Identity using (_==_)
open import Proposition.Sum
open import Logic
open import Function.Basic renaming (_$_ to _$'_) using ()

open import Proof
open import Proposition.Function using (_$_)
open import Function.Proof
open import Relation.Binary

open import Axiom.UniqueChoice

invertible-is-bijective : {f : (x : X) → Y} → invertible f ↔ Bijective f
⟶ (invertible-is-bijective {f = f}) (g , (g∘f~id , f∘g~id)) = record {}
  where
    instance
      Injective-f : Injective f
      inj ⦃ Injective-f ⦄ {x} {y} fx==fy =
        proof x
          〉 _==_ 〉 g (f x) :by: sym $ g∘f~id x
          〉 _==_ 〉 g (f y) :by: ap g fx==fy
          〉 _==_ 〉 y       :by: g∘f~id y
        qed
      Surjective-f : Surjective f
      sur ⦃ Surjective-f ⦄ y = g y , f∘g~id y
⟵ (invertible-is-bijective {X = X} {Y = Y} {f = f}) q =
  inverse , ((λ x → inj $ prop (!inv $' f x)) , λ y → prop (!inv y))
  where instance _ = q
        !inv : (y : Y) → Σₚ λ x → f x == y
        !inv y = !choice (!p $ sur y)
          where !p : (p : ∃ λ x → f x == y) → ∃! λ x → f x == y
                !p (x , p) = x , (p , λ x' p' → inj $ trans p' (sym p))
        inverse : (y : Y) → X
        inverse y = elem $' !inv y


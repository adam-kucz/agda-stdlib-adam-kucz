{-# OPTIONS --exact-split --prop #-}
module Function.Property.BijectionEquivalence where

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

invertible-is-bijective : {f : (x : X) → Y} → Invertible f ↔ Bijective f
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
      surj ⦃ Surjective-f ⦄ y = g y , f∘g~id y
⟵ (invertible-is-bijective {X = X} {Y = Y} {f = f}) q =
  inverse , ((λ x → inj $ prop (!inv $' f x)) , λ y → prop (!inv y))
  where instance _ = q
        !inv : (y : Y) → Σₚ λ x → f x == y
        !inv y = !choice (!p $ sur y)
          where !p : (p : ∃ λ x → f x == y) → ∃! λ x → f x == y
                !p (x , p) = x , (p , λ x' p' → inj $ trans p' (sym p))
        inverse : (y : Y) → X
        inverse y = elem $' !inv y


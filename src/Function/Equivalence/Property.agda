{-# OPTIONS --exact-split --safe --prop #-}
module Function.Equivalence.Property where

open import Universes
open import Function.Basic
open import Function.Equivalence.Definition
open import Proof

==→~ :
  {f g : Π A}
  (p : f == g)
  → -----------------
  f ~ g
==→~ (Idₚ.refl f) x = Het.refl (f x)

open import Relation.Binary.Property
  using (Reflexive; refl; Symmetric; sym; Transitive; trans)

instance
  Reflexive~ : Reflexive (_~_ {A = A})
  Symmetric~ : Symmetric (_~_ {A = A})
  Transitive~ : Transitive (_~_ {A = A})

refl ⦃ Reflexive~ ⦄ f x = refl (f x)
sym ⦃ Symmetric~ ⦄ p x = sym (p x)
trans ⦃ Transitive~ ⦄ {f}{g}{h} p q x =
  proof f x
    〉 Het._==_ 〉 g x :by: p x
    〉 Het._==_ 〉 h x :by: q x
  qed

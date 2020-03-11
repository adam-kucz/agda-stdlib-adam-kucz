{-# OPTIONS --exact-split --safe --prop #-}
module Relation.Binary.ReflexiveTransitiveClosure.Property where

open import Relation.Binary.ReflexiveTransitiveClosure.Definition
open import Relation.Binary.Definition
open import Relation.Binary.Property

open import Universes
open import Function.Proof

private variable R : BinRel 𝒰 X

instance
  Reflexive-rtc : Reflexive (refl-trans-close R)
  Transitive-rtc : Transitive (refl-trans-close R)
  InheritsSymmetric-rtc :
    ⦃ s : Symmetric R ⦄
    → -----------------------------
    Symmetric (refl-trans-close R)
  Subrelation-rtc : R ⊆ refl-trans-close R
  Subrelation-rtc2 :
    refl-trans-close (refl-trans-close R) ⊆ refl-trans-close R
  Subrelation-2-Subrelation-rtc :
    {P : BinRel 𝒱 X}
    ⦃ R⊆P : R ⊆ P ⦄
    → ----------------------------------------
    refl-trans-close R ⊆ refl-trans-close P
  Relating-rtc :
    {P : BinRel 𝒰 X}
    {R : BinRel 𝒱 Y}
    {f : (x : X) → Y}
    ⦃ _ : Relating f P R ⦄
    → ----------------------
    Relating f (refl-trans-close P) (refl-trans-close R)

refl ⦃ Reflexive-rtc ⦄ = rfl
trans ⦃ Transitive-rtc ⦄ (rfl _) q = q
trans ⦃ Transitive-rtc ⦄ (step s p) q = step s (trans p q)
sym ⦃ InheritsSymmetric-rtc ⦄ (rfl a) = rfl a
sym ⦃ InheritsSymmetric-rtc ⦄ (step aRb p) = step-right (sym p) (sym aRb)

subrel ⦃ Subrelation-rtc ⦄ {x} {y} xRy = step xRy (refl y)

subrel ⦃ Subrelation-rtc2 ⦄ (rfl a) = refl a
subrel ⦃ Subrelation-rtc2 ⦄ (step xR*z zR**y) =
  trans xR*z (subrel ⦃ Subrelation-rtc2 ⦄ zR**y)

subrel ⦃ Subrelation-2-Subrelation-rtc ⦄ {x} {x} (rfl x) = refl x
subrel ⦃ Subrelation-2-Subrelation-rtc ⦄ {x} {y} (step aRb bR*y) =
  step (subrel aRb) (subrel bR*y)

rel-preserv ⦃ Relating-rtc {f = f} ⦄ (rfl a) = rfl (f a)
rel-preserv ⦃ Relating-rtc ⦄ (step aRb aR*b) =
  step (rel-preserv aRb) (rel-preserv aR*b)

subrel-rtc-to-rtc-subrel-rtc :
  {P : BinRel 𝒱 X}
  ⦃ s : P ⊆ refl-trans-close R ⦄
  → -----------------------------------------
  refl-trans-close P ⊆ refl-trans-close R
subrel-rtc-to-rtc-subrel-rtc {R = _R_} {P = _P_} = go
  where go : refl-trans-close _P_ ⊆ refl-trans-close _R_
        subrel ⦃ go ⦄ (rfl a) = refl a
        subrel ⦃ go ⦄ (step {x} {b} {y} xPb bP*y) =
          trans (subrel xPb) (subrel ⦃ go ⦄ bP*y)

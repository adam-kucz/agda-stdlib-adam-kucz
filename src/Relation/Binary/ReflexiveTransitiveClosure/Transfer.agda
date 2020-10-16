{-# OPTIONS --exact-split --safe --prop #-}
open import Relation.Binary.Definition
open import Relation.Binary.Property
open import Relation.Binary.ReflexiveTransitiveClosure.Definition
  renaming (refl-trans-close to rtc)

open import Universes

module Relation.Binary.ReflexiveTransitiveClosure.Transfer
  (R : BinRel 𝒰 X)
  (single-step : BinRel 𝒱 X)
  ⦃ equiv : R ~ rtc single-step ⦄
  where

open import Proposition.Function using (_$_)
open import Function.Proof

open import Relation.Binary.ReflexiveTransitiveClosure.Property

instance
  ReflexiveR : Reflexive R
  TransitiveR : Transitive R

InheritsSymmetricR :
  ⦃ symmetric : Symmetric single-step ⦄
  → ----------------------------------------
  Symmetric R
InheritsRelatingR :
  {single-step-P : BinRel 𝒲 Y}
  {P : BinRel 𝒯 Y}
  ⦃ equiv : P ~ rtc single-step-P ⦄
  {f : X → Y}
  ⦃ ss-rel : Relating f single-step single-step-P ⦄
  → ----------------------
  Relating f R P

refl ⦃ ReflexiveR ⦄ x = subrel $ refl x
trans ⦃ TransitiveR ⦄ p q = subrel $ trans (subrel p) (subrel q)

sym ⦃ InheritsSymmetricR ⦄ p = subrel $ sym $ subrel p
rel-preserv ⦃ InheritsRelatingR ⦄ aRb = subrel $ rel-preserv $ subrel aRb

Subrelation-rtcR-R : rtc R ⊆ R
subrel⊆ Subrelation-rtcR-R p =
  subrel $ subrel $ subrel {sup = rtc (rtc single-step)} p

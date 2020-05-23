{-# OPTIONS --exact-split --safe --prop #-}
module Type.BinarySum.Property where

open import Type.BinarySum.Definition

open import Universes
open import Proposition.Identity
open import Function

[_,_]∘[_+_] :
  (g₀ : (x : X₁) → Z)
  (g₁ : (y : Y₁) → Z)
  (f₀ : (x : X₀) → X₁)
  (f₁ : (y : Y₀) → Y₁)
  → -----------------------
  [ g₀ , g₁ ] ∘ [ f₀ + f₁ ] ~ [ g₀ ∘ f₀ , g₁ ∘ f₁ ]
[ g₀ , g₁ ]∘[ f₀ + f₁ ] (inl x) = Het.refl (g₀ (f₀ x))
[ g₀ , g₁ ]∘[ f₀ + f₁ ] (inr y) = Het.refl (g₁ (f₁ y))

[_+_]∘[_+_] :
  (g₀ : (x : X₁) → X₂)
  (g₁ : (y : Y₁) → Y₂)
  (f₀ : (x : X₀) → X₁)
  (f₁ : (y : Y₀) → Y₁)
  → -----------------------
  [ g₀ + g₁ ] ∘ [ f₀ + f₁ ] ~ [ g₀ ∘ f₀ + g₁ ∘ f₁ ]
[ g₀ + g₁ ]∘[ f₀ + f₁ ] (inl x) = Het.refl (inl (g₀ (f₀ x)))
[ g₀ + g₁ ]∘[ f₀ + f₁ ] (inr y) = Het.refl (inr (g₁ (f₁ y)))

_∘[_,_] :
  (g : (z : Z₀) → Z₁)
  (f₀ : (x : X) → Z₀)
  (f₁ : (y : Y) → Z₀)
  → -----------------------
  g ∘ [ f₀ , f₁ ] ~ [ g ∘ f₀ , g ∘ f₁ ]
(g ∘[ f₀ , f₁ ]) (inl x) = Het.refl (g (f₀ x))
(g ∘[ f₀ , f₁ ]) (inr y) = Het.refl (g (f₁ y))

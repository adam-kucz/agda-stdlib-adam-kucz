{-# OPTIONS --exact-split --safe --prop #-}
module Data.Monad.Property where

open import Data.Monad.Definition

open import Data.Functor

open import Universes
open import Function hiding (_$_)
open import Proof

fmap-bind₀ : {X : 𝒰 ˙}{Y : 𝒱 ˙}{Z : 𝒲 ˙}
  {U : ∀ {𝒰} → 𝒰 ˙ → Universe}
  {M : ∀ {𝒰}(X : 𝒰 ˙) → U X ˙}
  ⦃ _ : Monad M ⦄
  (m : M X)
  (f : X → Y)
  (g : Y → M Z)
  → ----------------------------
  fmap f m >>= g == m >>= g ∘ f
fmap-bind₀ m f g =
  ap (λ — → join (— m)) $ sym {R = _==_} $ fmap-∘ g f

fmap-bind₁ : {X : 𝒰 ˙}{Y : 𝒱 ˙}{Z : 𝒲 ˙}
  {U : ∀ {𝒰} → 𝒰 ˙ → Universe}
  {M : ∀ {𝒰}(X : 𝒰 ˙) → U X ˙}
  ⦃ _ : Monad M ⦄
  (m : M X)
  (f : X → M Y)
  (g : Y → Z)
  → ----------------------------
  fmap g (m >>= f) == m >>= fmap g ∘ f
fmap-bind₁ m f g =
  proof fmap g (m >>= f)
    === fmap g (join (fmap f m))
      :by: Id.refl _
    === join (fmap (fmap g) (fmap f m))
      :by: ap (λ — → — (fmap f m)) $
           sym {R = _==_} $ mon-naturality g
    === join (fmap (fmap g ∘ f) m)
      :by: fmap-bind₀ m f (fmap g) 
    === m >>= fmap g ∘ f
      :by: Id.refl _
  qed

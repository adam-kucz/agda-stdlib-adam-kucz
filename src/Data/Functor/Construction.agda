{-# OPTIONS --exact-split --safe --prop #-}
module Data.Functor.Construction where

open import Data.Functor.Definition

open import Universes
open import Function hiding (_$_)

instance
    ComposeFunctor :
      {U : ∀ {𝒰} → 𝒰 ˙ → Universe}
      {F : ∀ {𝒰}(X : 𝒰 ˙) → U X ˙}
      ⦃ F₀ : Functor F ⦄
      {V : ∀ {𝒰} → 𝒰 ˙ → Universe}
      {G : ∀ {𝒰}(X : 𝒰 ˙) → V X ˙}
      ⦃ G₀ : Functor G ⦄
      → ----------------------------
      Functor (λ X → F (G X))

open import Proof

fmap ⦃ ComposeFunctor ⦃ F₀ ⦄ ⦃ G₀ ⦄ ⦄ = fmap ⦃ F₀ ⦄ ∘ fmap ⦃ G₀ ⦄
fmap-id ⦃ ComposeFunctor ⦃ F₀ ⦄ ⦃ G₀ ⦄ ⦄ =
  proof fmap ⦃ F₀ ⦄ (fmap ⦃ G₀ ⦄ id)
    === fmap ⦃ F₀ ⦄ id
      :by: ap (fmap ⦃ F₀ ⦄) {r' = _==_} $ fmap-id ⦃ G₀ ⦄
    === id
      :by: fmap-id ⦃ F₀ ⦄
  qed 
fmap-∘ ⦃ ComposeFunctor ⦃ F₀ ⦄ ⦃ G₀ ⦄ ⦄ g f =
  proof fmapf (fmapg (g ∘ f))
    === fmapf (fmapg g ∘ fmapg f)
      :by: ap fmapf $ fmap-∘ ⦃ G₀ ⦄ g f
    === fmapf (fmapg g) ∘ fmapf (fmapg f)
      :by: fmap-∘ ⦃ F₀ ⦄ (fmapg g) (fmapg f)
  qed
  where fmapf = fmap ⦃ F₀ ⦄
        fmapg = fmap ⦃ G₀ ⦄

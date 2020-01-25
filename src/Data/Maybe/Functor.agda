{-# OPTIONS --exact-split --prop #-}
module Data.Maybe.Functor where

open import Data.Maybe.Definition
open import Data.Functor

open import Proposition.Identity

open import Axiom.FunctionExtensionality

instance
  MaybeFunctor : Functor (λ X → Maybe X)
  fmap ⦃ MaybeFunctor ⦄ _ nothing = nothing
  fmap ⦃ MaybeFunctor ⦄ f (just x) = just (f x)
  fmap-id ⦃ MaybeFunctor ⦄ = fun-ext λ
    { nothing → refl nothing
    ; (just x) → refl (just x) }
  fmap-∘ ⦃ MaybeFunctor ⦄ f g = fun-ext λ
    { nothing → refl nothing
    ; (just x) → refl (just (f (g x)))}


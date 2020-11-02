{-# OPTIONS --exact-split --prop #-}
module Data.Maybe.Functor where

open import Data.Maybe.Definition
open import Data.Functor
open import Data.Applicative
open import Data.Monad

open import Proof

open import Axiom.FunctionExtensionality

instance
  MaybeFunctor : Functor (λ X → Maybe X)
  MaybeApplicative : Applicative (λ X → Maybe X)
  MaybeMonad : Monad (λ X → Maybe X)

fmap ⦃ MaybeFunctor ⦄ _ nothing = nothing
fmap ⦃ MaybeFunctor ⦄ f (just x) = just (f x)
fmap-id ⦃ MaybeFunctor ⦄ = subrel $ fun-ext λ
  { nothing → refl nothing
  ; (just x) → refl (just x) }
fmap-∘ ⦃ MaybeFunctor ⦄ f g = subrel {sup = _==_} $ fun-ext λ
  { nothing → refl nothing
  ; (just x) → refl (just (f (g x)))}

open import Type.Unit
open import Type.Sum

functor ⦃ MaybeApplicative ⦄ = MaybeFunctor
unit ⦃ MaybeApplicative ⦄ = just ⋆
_⋆_ ⦃ MaybeApplicative ⦄ nothing _ = nothing
_⋆_ ⦃ MaybeApplicative ⦄ (just _) nothing = nothing
_⋆_ ⦃ MaybeApplicative ⦄ (just x)(just y) = just (x , y)
fmap-def ⦃ MaybeApplicative ⦄ _ nothing = Id.refl nothing
fmap-def ⦃ MaybeApplicative ⦄ f (just x) = Id.refl (just (f x))
naturality ⦃ MaybeApplicative ⦄ f g nothing v = Id.refl nothing
naturality ⦃ MaybeApplicative ⦄ f g (just x) nothing = Id.refl nothing
naturality ⦃ MaybeApplicative ⦄ f g (just x) (just y) =
  Id.refl (just (f x , g y))
left-identity ⦃ MaybeApplicative ⦄ nothing = Id.refl nothing
left-identity ⦃ MaybeApplicative ⦄ (just x) = Id.refl (just x)
right-identity ⦃ MaybeApplicative ⦄ nothing = Id.refl nothing
right-identity ⦃ MaybeApplicative ⦄ (just x) = Id.refl (just x)
⋆-assoc ⦃ MaybeApplicative ⦄ nothing _ _ = Id.refl nothing
⋆-assoc ⦃ MaybeApplicative ⦄ (just _) nothing _ = Id.refl nothing
⋆-assoc ⦃ MaybeApplicative ⦄ (just _)(just _) nothing =
  Id.refl nothing
⋆-assoc ⦃ MaybeApplicative ⦄ (just x)(just y)(just z) =
  Id.refl (just (x , y , z))

applicative ⦃ MaybeMonad ⦄ = MaybeApplicative
join ⦃ MaybeMonad ⦄ nothing = nothing
join ⦃ MaybeMonad ⦄ (just m) = m
⋆-def ⦃ MaybeMonad ⦄ nothing _ = Id.refl nothing
⋆-def ⦃ MaybeMonad ⦄ (just _) nothing = Id.refl nothing
⋆-def ⦃ MaybeMonad ⦄ (just x)(just y) = Id.refl (just (x , y))
associativity ⦃ MaybeMonad ⦄ = subrel $ fun-ext λ
  { nothing → Het.refl nothing
  ; (just nothing) → Het.refl nothing
  ; (just (just x)) → Het.refl x}
Monad.unit1 MaybeMonad = subrel $ fun-ext λ
  { nothing → Het.refl nothing
  ; (just x) → Het.refl (just x)}
Monad.unit2 MaybeMonad = subrel $ fun-ext λ
  { nothing → Het.refl nothing
  ; (just x) → Het.refl (just x)}
Monad.naturality MaybeMonad f = subrel $ fun-ext λ
  { nothing → Het.refl nothing
  ; (just nothing) → Het.refl nothing 
  ; (just (just x)) → Het.refl (just (f x))}

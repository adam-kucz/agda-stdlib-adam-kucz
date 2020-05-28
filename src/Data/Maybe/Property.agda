{-# OPTIONS --exact-split --prop --safe #-}
module Data.Maybe.Property where

open import Data.Maybe.Definition

open import Universes
open import Proposition.Decidable
open import Proposition.Identity

instance
  MaybeHasDecidableIdentity :
    ⦃ d== : HasDecidableIdentity X ⦄
    → ----------------------------------------
    HasDecidableIdentity (Maybe X)

MaybeHasDecidableIdentity {x = nothing}{nothing} = true (refl nothing)
MaybeHasDecidableIdentity {x = nothing}{just _} = false λ ()
MaybeHasDecidableIdentity {x = just x}{nothing} = false λ ()
MaybeHasDecidableIdentity {x = just x}{just y} with decide (x == y)
MaybeHasDecidableIdentity {x = just x}{just y} | true p = true (ap just p)
MaybeHasDecidableIdentity {x = just x}{just y} | false ¬p =
  false λ { (refl (just x)) → ¬p (refl x)}

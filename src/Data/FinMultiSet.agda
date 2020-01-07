{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Data.List renaming (_∈_ to member)
open import Proposition.Permutation hiding (refl)
open import Relation.Binary.Property
open import Type.Quotient

module Data.FinMultiSet {X : 𝒰 ˙} where

open Quotient (List X) Perm ⦃ DefaultEquivalence ⦄
  renaming (Type to QuotType)

FinMultiSet : (X : 𝒰 ˙) → 𝒰 ⁺ ˙
FinMultiSet X = QuotType

open import Proposition.Sum
open import Proposition.Identity hiding (refl)

∅ : FinMultiSet X
∅ = Perm [] , ([] , λ l → refl (Perm [] l))

singleton : (x : X) → FinMultiSet X
singleton x = Perm [ x ] , ([ x ] , λ l → refl (Perm [ x ] l))

infixr 112 _∈_
_∈_ : (x : X) (l : FinMultiSet X) → 𝒰 ᵖ
_∈_ x (e , p) = {!elim !}
  where go : (∃ (λ (l : List X) → (l' : List X) → e l' == Perm l l')) → 𝒰 ᵖ
        go x = {!!}

-- toSet :
--   ⦃ _ : {x y : X} → Decidable (x == y) ⦄
--   (l : List X)
--   → -------------------------
--   FinSet X




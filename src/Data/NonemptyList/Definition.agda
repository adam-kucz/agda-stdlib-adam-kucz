{-# OPTIONS --safe --exact-split --prop  #-}
module Data.NonemptyList.Definition where

open import Universes

infixr 115 _∷_
data NonemptyList (X : 𝒰 ˙) : 𝒰 ˙ where
  [_]  : (x : X) → NonemptyList X
  _∷_ : (h : X) (t : NonemptyList X) → NonemptyList X

pattern [_⸴_] a₀ a₁ = a₀ ∷ [ a₁ ]
pattern [_⸴_⸴_] a₀ a₁ a₂ = a₀ ∷ a₁ ∷ [ a₂ ]
pattern [_⸴_⸴_⸴_] a₀ a₁ a₂ a₃ = a₀ ∷ a₁ ∷ a₂ ∷ [ a₃ ]



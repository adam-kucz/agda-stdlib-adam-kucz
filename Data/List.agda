{-# OPTIONS --safe --exact-split --prop  #-}
module Data.List where

open import PropUniverses

infixr 115 _∷_
data List (X : 𝒰 ˙) : 𝒰 ˙ where
  []  : List X
  _∷_ : (h : X) (t : List X) → List X

open import Data.Nat
  using (ℕ; zero; suc; _+_; _<_; s<s→-<-)

len : (l : List X) → ℕ
len [] = 0
len (x ∷ l) = 1 + len l

infixr 110 _!_[_]
_!_[_] : (l : List X) (n : ℕ) (p : n < len l) → X
h ∷ _ ! zero [ _ ] = h
_ ∷ l ! suc n [ p ] = l ! n [ s<s→-<- p ]

infixr 112 _∈_
data _∈_ {X : 𝒰 ˙} (x : X) : (l : List X) → 𝒰 ᵖ where
  x∈x∷_ : (t : List X) → x ∈ x ∷ t
  x∈tail : (h : X) {t : List X} (p : x ∈ t) → x ∈ h ∷ t

pattern [_] a₀ = a₀ ∷ []
pattern [_⸴_] a₀ a₁ = a₀ ∷ a₁ ∷ []
pattern [_⸴_⸴_] a₀ a₁ a₂ = a₀ ∷ a₁ ∷ a₂ ∷ []
pattern [_⸴_⸴_⸴_] a₀ a₁ a₂ a₃ = a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ []


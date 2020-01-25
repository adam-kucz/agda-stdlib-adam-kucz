{-# OPTIONS --safe --exact-split --prop  #-}
open import PropUniverses

module Data.List.Definition {𝒰 : Universe} where

infixr 115 _∷_
data List (X : 𝒰 ˙) : 𝒰 ˙ where
  []  : List X
  _∷_ : (h : X) (t : List X) → List X

open import Data.Nat.Definition using (ℕ; zero; suc)
open import Data.Nat.Syntax
open Pattern
open import Data.Nat.Order using (_<_; s<s→-<-)

len : (l : List X) → ℕ
len [] = 0
len (x ∷ l) = len l +1

infixr 110 _!_[_]
_!_[_] : (l : List X) (n : ℕ) (p : n < len l) → X
h ∷ _ ! zero [ _ ] = h
_ ∷ l ! suc n [ p ] = l ! n [ s<s→-<- p ]

open import Proposition.Identity
open import Proposition.Empty

last : (l : List X)(p : l ≠ [] {X}) → X
last {X = X} [] p = ⊥-recursion X (p (refl []))
last (x ∷ []) p = x
last (_ ∷ h ∷ l) p = last (h ∷ l) (λ ())

List== :
  {h h' : X}
  {t t' : List X}
  (p : h == h')
  (q : t == t')
  → ---------------
  h ∷ t == h' ∷ t'
List== (refl h) (refl t) = refl (h ∷ t)

pattern [_] a₀ = a₀ ∷ []
pattern [_⸴_] a₀ a₁ = a₀ ∷ a₁ ∷ []
pattern [_⸴_⸴_] a₀ a₁ a₂ = a₀ ∷ a₁ ∷ a₂ ∷ []
pattern [_⸴_⸴_⸴_] a₀ a₁ a₂ a₃ = a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ []



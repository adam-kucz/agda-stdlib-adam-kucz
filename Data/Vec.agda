{-# OPTIONS --safe --exact-split --prop  #-}
module Data.Vec where

open import PropUniverses
open import Data.Nat

infixr 115 _∷_
data Vec (X : 𝒰 ˙) : (n : ℕ) → 𝒰 ˙ where
  []  : Vec X 0
  _∷_ : ∀ {n} (h : X) (t : Vec X n) → Vec X (suc n)

open import Data.Nat
  using (ℕ; zero; suc; _+_; _<_; s<s→-<-)

infixr 110 _!_[_]
_!_[_] : ∀ {m} (l : Vec X m) (n : ℕ) (p : n < m) → X
h ∷ _ ! zero [ _ ] = h
_ ∷ l ! suc n [ p ] = l ! n [ s<s→-<- p ]

infixr 112 _∈_
data _∈_ {X : 𝒰 ˙} (x : X) : {n : ℕ} (l : Vec X n) → 𝒰 ᵖ where
  x∈x∷_ : ∀ {n} (t : Vec X n) → x ∈ x ∷ t
  x∈tail : ∀ {n} (h : X) {t : Vec X n} (p : x ∈ t) → x ∈ h ∷ t

pattern [_] a₀ = a₀ ∷ []
pattern [_⸴_] a₀ a₁ = a₀ ∷ a₁ ∷ []
pattern [_⸴_⸴_] a₀ a₁ a₂ = a₀ ∷ a₁ ∷ a₂ ∷ []
pattern [_⸴_⸴_⸴_] a₀ a₁ a₂ a₃ = a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ []

open import Prop'.Identity
open import Logic

Vec== : ∀ {m}
  {h1 h2 : X} {t1 t2 : Vec X m}
  → -----------------------------------------
  h1 ∷ t1 == h2 ∷ t2 ↔ h1 == h2 ∧ t1 == t2
⟶ Vec== (refl (h ∷ t)) = refl h , refl t
⟵ Vec== (refl h , refl t) = refl (h ∷ t)

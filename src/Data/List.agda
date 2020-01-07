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

open import Proposition.Identity
open import Proposition.Decidable
open import Data.Maybe
open import Data.Functor

find :
  ⦃ _ : {x y : X} → Decidable (x == y) ⦄
  (x : X)
  (l : List X)
  → ---------------------------------------
  Maybe ℕ
find x [] = nothing
find x (h ∷ l) with decide (x == h)
find x (h ∷ l) | true  _ = just 0
find x (h ∷ l) | false _ = fmap suc (find x l)

index :
  ⦃ _ : {x y : X} → Decidable (x == y) ⦄
  {x : X}
  {l : List X}
  (p : x ∈ l)
  → ---------------------------------------
  ℕ
index {x = x} {h ∷ l} p with decide (x == h)
index {x = x} {h ∷ l} p | true   x==h = 0
index {x = x} {h ∷ l} p | false ¬x==h = suc (index (prev p))
  where open import Proposition.Empty
        prev : (p : x ∈ h ∷ l) → x ∈ l
        prev (x∈x∷ t) = ⊥-recursionₚ (x ∈ l) (¬x==h (refl x))
        prev (x∈tail _ p) = p

multiplicity : 
  ⦃ _ : {x y : X} → Decidable (x == y) ⦄
  (x : X)
  (l : List X)
  → ---------------------------------------
  ℕ
multiplicity x [] = 0
multiplicity x (h ∷ l) with decide (x == h)
multiplicity x (h ∷ l) | true  _ = suc (multiplicity x l)
multiplicity x (h ∷ l) | false _ = multiplicity x l

pattern [_] a₀ = a₀ ∷ []
pattern [_⸴_] a₀ a₁ = a₀ ∷ a₁ ∷ []
pattern [_⸴_⸴_] a₀ a₁ a₂ = a₀ ∷ a₁ ∷ a₂ ∷ []
pattern [_⸴_⸴_⸴_] a₀ a₁ a₂ a₃ = a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ []

remove-at : (n : ℕ) (l : List X) (p : n < len l) → List X
remove-at zero    (h ∷ l) p = l
remove-at (suc n) (h ∷ l) p = remove-at n l (s<s→-<- p)

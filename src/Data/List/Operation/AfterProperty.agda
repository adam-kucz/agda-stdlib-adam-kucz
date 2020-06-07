{-# OPTIONS --safe --exact-split --prop  #-}
module Data.List.Operation.AfterProperty where

open import Data.List.Definition
open import Data.List.Property

open import Universes
open import Type.Sum hiding (_,_)
open import Collection
open import Data.Nat
open import Proof

infixr 110 _!_[_]
_!_[_] : (l : List X)(n : ℕ)(p : n +1 ≤ len l) → X
h ∷ _ ! zero [ _ ] = h
_ ∷ l ! suc n [ p ] = l ! n [ ap pred p ]

zip : (l₀ : List X)(l₁ : List Y)(p : len l₀ == len l₁) → List (X × Y)
zip [] [] p = []
zip (h₀ ∷ l₀) (h₁ ∷ l₁) p = (h₀ Σ., h₁) ∷ zip l₀ l₁ (ap pred p)

open import Proposition.Sum
open import Data.List.Collection
open import Logic

∈-zip : ∀{X : 𝒰 ˙}{Y : 𝒱 ˙}
  (l₀ : List X)
  (l₁ : List Y)
  (p : len l₀ == len l₁)
  {x : X}{y : Y}
  → -----------------------
  let p' : ∀{i}(p : i +1 ≤ len l₀) → i +1 ≤ len l₁
      p' {i} = Id.coe (ap (i +1 ≤_) p) in
  x Σ., y ∈ zip l₀ l₁ p
  ↔
  ∃ λ i →
    i +1 ≤ len l₀ ∧ᵈ
    λ p → l₀ ! i [ p ] == x ∧ l₁ ! i [ p' p ] == y
⟶ (∈-zip [] [] p) ()
⟵ (∈-zip [] [] p) (_ , ())
⟶ (∈-zip (h₀ ∷ l₀) (h₁ ∷ l₁) p) (x∈x∷ _) =
  0 , (s≤s $ z≤ len l₀ , (Id.refl h₀ , Id.refl h₁))
⟶ (∈-zip (h₀ ∷ l₀) (h₁ ∷ l₁) p) (x∈tail _ q)
  with ⟶ (∈-zip l₀ l₁ (ap pred p)) q
⟶ (∈-zip (h₀ ∷ l₀) (h₁ ∷ l₁) p) (x∈tail _ q)
  | i , (i+1≤len-l₀ , eqs) = i +1 , (s≤s i+1≤len-l₀ , eqs)
⟵ (∈-zip (h₀ ∷ l₀) (h₁ ∷ l₁) p) (zero , (_ , (Id.refl _ , Id.refl _))) =
  x∈x∷ (zip l₀ l₁ (ap pred p))
⟵ (∈-zip (h₀ ∷ l₀) (h₁ ∷ l₁) p) (i +1 , (s≤s i+1≤len , eqs)) =
  x∈tail (h₀ Σ., h₁) $ ⟵ (∈-zip l₀ l₁ (ap pred p)) (i , (i+1≤len , eqs))

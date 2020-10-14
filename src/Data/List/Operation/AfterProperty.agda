{-# OPTIONS --safe --exact-split  #-}
module Data.List.Operation.AfterProperty where

open import Data.List.Definition
open import Data.List.Property

open import Universes
open import Type.Sum
open import Collection
open import Data.Nat
open import Data.Maybe
open import Proof

infixr 110 _!_
_!_ : (l : List X)(n : ℕ) → Maybe X
[] ! _ = nothing
h ∷ _ ! 0 = just h
_ ∷ l ! (n +1) = l ! n

zip : (l₀ : List X)(l₁ : List Y) → List (X × Y)
zip [] _ = []
zip (_ ∷ _) [] = []
zip (h₀ ∷ l₀)(h₁ ∷ l₁) = (h₀ , h₁) ∷ zip l₀ l₁

open import Data.List.Collection
open import Logic

∈-zip : ∀{X : 𝒰 ˙}{Y : 𝒱 ˙}
  (l₀ : List X)
  (l₁ : List Y)
  {x : X}{y : Y}
  → -----------------------
  (x , y) ∈ zip l₀ l₁
  ↔
  ∃ λ i → i + 1 ≤ len l₀ ∧ (l₀ ! i == just x ∧ l₁ ! i == just y)
⟶ (∈-zip (h₀ ∷ l₀) (h₁ ∷ l₁)) (x∈x∷ .(zip l₀ l₁)) =
  0 , (s≤s (z≤ len l₀) , (Id.refl (just h₀) , Id.refl (just h₁)))
⟶ (∈-zip (h₀ ∷ l₀) (h₁ ∷ l₁)) (x∈tail .(h₀ , h₁) p) with ⟶ (∈-zip l₀ l₁) p
... | i , (q , q') =
  i +1 , (ap suc ⦃ Relating-+-left-≤ ⦄ q , q')
⟵ (∈-zip (h ∷ l₀) (h₁ ∷ l₁))
  (0 , (_ , (Id.refl .(just h) , Id.refl .(just h₁)))) = x∈x∷ (zip l₀ l₁)
⟵ (∈-zip (h₀ ∷ l₀) (h₁ ∷ l₁)) (i +1 , (s≤s q , eqs)) =
  x∈tail (h₀ , h₁) $ ⟵ (∈-zip l₀ l₁) (i , (q , eqs))

{-# OPTIONS --exact-split --safe --prop #-}
module Structure.Monoid.Property where

open import Structure.Monoid.Definition
open import Structure.Monoid.Function

open import Universes
open import Data.Collection
open import Data.List
open import Data.List.Monoid
open import Logic
open import Proof
  
∈mconcat : ∀ ls (x : X)
  → ---------------------------------------
  x ∈ mconcat ls ↔ ∃ λ (l : List X) → l ∈ ls ∧ x ∈ l
⟶ (∈mconcat (h ∷ ls) x) p with ⟶ (∈++ x h (mconcat ls)) p
⟶ (∈mconcat (h ∷ ls) x) p | ∨left p₁ = h , (x∈x∷ ls , p₁)
⟶ (∈mconcat (h ∷ ls) x) p | ∨right q with ⟶ (∈mconcat ls x) q
⟶ (∈mconcat (h ∷ ls) x) p | ∨right q | l , (p₁ , p₂) = l , (x∈tail h p₁ , p₂)
⟵ (∈mconcat (l ∷ t) x) (l , (x∈x∷ t , q)) =
  ⟵ (∈++ x l (mconcat t)) (∨left q)
⟵ (∈mconcat (h ∷ t) x) (l , (x∈tail h p , q)) =
  ⟵ (∈++ x h (mconcat t)) $ ∨right $ ⟵ (∈mconcat t x) (l , (p , q))

open import Operation.Binary

mconcat-zero : ∀ {l}
  ⦃ mon : Monoid X ⦄
  {z : X}
  ⦃ zero : z IsZeroOf _∙_ ⦄
  (q : z ∈ l)
  → --------------------
  mconcat l == z
mconcat-zero (x∈x∷ l) = left-zero (mconcat l)
mconcat-zero {l = h ∷ t}{z = z} ⦃ zero ⦄ (x∈tail h q) =
  proof h ∙ mconcat t
    === h ∙ z :by: ap (h ∙_) $ mconcat-zero ⦃ zero = zero ⦄ q 
    === z     :by: right-zero h
  qed

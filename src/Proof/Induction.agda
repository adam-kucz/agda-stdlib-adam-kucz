{-# OPTIONS --exact-split --safe --prop #-}
open import PropUniverses
open import Relation.Binary

module Proof.Induction where

open import Type.Subset hiding (_⊆_)
open import Proposition.Decidable
open import Proposition.Sum using (_,_)

on-elems : {S : Subset 𝒰 X}
  (_R_ : Rel 𝒱 X X)
  → ------------------------------
  Rel 𝒱 (SubsetType X S) (SubsetType X S)
on-elems _R_ (x , _) (x' , _) = x R x'

record WellFounded (_≤_ : Rel 𝒰 X X) : 𝒰ω where
  field
    min :
      (S : Subset 𝒲 X)
      ⦃ _ : ∀ {x : X} → Decidable (x ∈ S) ⦄
      (non-empty : SubsetType X S)
      → ------------------------
      SubsetType X S
    well-founded :
      (S : Subset 𝒲 X)
      ⦃ _ : ∀ {x : X} → Decidable (x ∈ S) ⦄
      (non-empty : SubsetType X S)
      → -----------------------
      Minimal (on-elems _≤_) (min S non-empty)

open WellFounded ⦃ … ⦄ public

open import Type.Finite

record FiniteBoundedSubsets {X : 𝒰 ˙}(_≤_ : Rel 𝒱 X X): 𝒰 ⊔ 𝒱 ᵖ where
  field
    finite : ∀ (y : X) → is-finite (SubsetType X (_≤ y))

open FiniteBoundedSubsets ⦃ … ⦄ public

open import Collection
open import Data.Nat hiding (_≤_)
open import Data.Vec
open import Logic

complete-induction :
  {𝐴 : (x : X) → 𝒰 ᵖ}
  (_<_ : Rel 𝒱 X X)
  ⦃ wf : WellFounded _<_ ⦄
  ⦃ fin : FiniteBoundedSubsets _<_ ⦄
  (p : ∀ y (ih : ∀ x (q : x < y) → 𝐴 x) → 𝐴 y)
  → -----------------------
  ∀ x → 𝐴 x
complete-induction {X = X}{𝐴 = 𝐴} _<_ p x =
  go ∅ (λ ()) (finite x) (?) (refl (finite x))
  where go : (S₀ : a subset)
             (p₀ : certificate that ∀ x ∈ S₀ → 𝐴 x)
             (S₁ : set which we still need to show 𝐴)
             (p₁ : certificate that ∀ x' < x ∧ (∃ y → y is minimal S₁ → x' < y) → x' ∈ S₀)
             (q : certificate that S₀ ∪ S₁ == set (_< x))
             → -------------------------------------------
             for all (_< x) have 𝐴
        go S₀ p₀ [] p₁ q = done by p₀ q
        go S₀ p₀ S₁ p₁ q =
          let x == min of S₁
              p₀' : 𝐴 x = from p with args p₁, p₀ and S₀ to have 𝐴 x
              S₀' = insert x S₀
              S₁' = remove x S₁
              p₁ ' = λ x < min S₁' →
                have x < min S₁ or x ≮ min S₁
                  first by p₁
                  second by ?
          go S₀' (p₀ ∧ p₀') S₁' p₁' (q with insert-valid, remove-valid)

x < min (S₁ \ {min S₁})
x ≮ min S₁

let y = min S₁
have ∀ z ∈ S₁ ∧ z < y → z == y

a  <  b
^ |-
    d
c

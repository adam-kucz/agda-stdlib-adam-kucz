{-# OPTIONS --exact-split --safe --prop #-}
module Type.Enumerable.Definition where

open import PropUniverses
open import Type.Finite
open import Data.List renaming ([_] to L[_])
open import Data.Vec renaming ([_] to V[_])
open import Collection
open import Logic

open import Proposition.Sum

is-enumerable : (X : 𝒰 ˙) → 𝒰 ˙
is-enumerable X = Σₚ λ (l : List X) → contains-all X l
  
open import Type.Sum renaming (_,_ to _Σ,_)

Enumerable : (𝒰 : Universe) → 𝒰 ⁺ ˙
Enumerable 𝒰 = Σ λ (X : 𝒰 ˙) → is-enumerable X

open import Data.Nat
open import Proposition.Decidable
open import Function hiding (_$_)
open import Proof

vec-uniq : (v : Vec X n) → 𝒰₀ ᵖ
vec-uniq [] = ⊤
vec-uniq (h ∷ v) = h ∉ v ∧ vec-uniq v

card :
  (Enum : Enumerable 𝒰) →
  let X = pr₁ Enum in
  ⦃ dec : HasDecidableIdentity X ⦄
  → ----------------------------------------------------------
  Σₚ λ n → ∃ λ (v : Vec X n) → contains-all X v ∧ vec-uniq v
card (X Σ, (l , p)) ⦃ dec ⦄ = go l [] (λ x → ∨right $ p x) ⋆ₚ
  where go : (l : List X)
             (v : Vec X n)
             (p : ∀(x : X) → x ∈ v ∨ x ∈ l)
             (q : vec-uniq v)
             → ------------------------------
             Σₚ λ n → ∃ λ (v : Vec X n) → contains-all X v ∧ vec-uniq v
        go {n} [] v p q = n , (v , (all-in , q))
          where all-in : contains-all X v
                all-in x with ∨left x∈v ← p x = x∈v
        go (h ∷ l) v p q with decide (h ∈ v)
        ... | true h∈v = go l v p' q
          where p' : ∀(x : X) → x ∈ v ∨ x ∈ l
                p' x with p x
                ... | ∨left x∈v = ∨left x∈v
                ... | ∨right (x∈x∷ l) = ∨left h∈v
                ... | ∨right (x∈tail h x∈l) = ∨right x∈l
        ... | false h∉v = go l (h ∷ v) p' (h∉v , q)
          where p' : ∀(x : X) → x ∈ h ∷ v ∨ x ∈ l
                p' x with p x
                ... | ∨left x∈v = ∨left (x∈tail h x∈v)
                ... | ∨right (x∈x∷ l) = ∨left (x∈x∷ v)
                ... | ∨right (x∈tail h x∈l) = ∨right x∈l

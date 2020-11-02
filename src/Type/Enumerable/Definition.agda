{-# OPTIONS --exact-split --safe #-}
module Type.Enumerable.Definition where

open import Universes
open import Type.Finite
open import Data.List renaming ([_] to L[_])
open import Data.Vec renaming ([_] to V[_])
open import Collection
open import Logic

is-enumerable : (X : 𝒰 ˙) → 𝒰 ˙
is-enumerable X = ∃ λ (l : List X) → contains-all X l
  
open import Type.Sum

Enumerable : (𝒰 : Universe) → 𝒰 ⁺ ˙
Enumerable 𝒰 = Σ λ (X : 𝒰 ˙) → is-enumerable X

open import Data.Nat
open import Type.Decidable
open import Function
open import Proof

vec-uniq : (v : Vec X n) → 𝒰₀ ˙
vec-uniq [] = ⊤
vec-uniq (h ∷ v) = h ∉ v ∧ vec-uniq v

card :
  (Fin : Enumerable 𝒰) →
  let X = elem Fin in
  ⦃ dec : HasDecidableIdentity X ⦄
  → ----------------------------------------------------------
  Σ λ n → ∃ λ (v : Vec X n) → contains-all X v ∧ vec-uniq v
card (X , (l , p)) ⦃ dec ⦄ = go l [] (∨right ∘ p) ⋆
  where go : (l : List X)
             (v : Vec X n)
             (p : ∀(x : X) → x ∈ v ∨ x ∈ l)
             (q : vec-uniq v)
             → ------------------------------
             Σ λ n → ∃ λ (v : Vec X n) → contains-all X v ∧ vec-uniq v
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

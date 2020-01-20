{-# OPTIONS --exact-split --exact-split --safe --prop #-}
module Type.Finite where

open import PropUniverses
open import Logic
open import Proposition.Identity using (_==_; _≠_; refl; ap)
open import Data.Nat using (ℕ)
open import Data.FinNat using (Finℕ; toℕ; toℕ<)
open import Data.Vec
open import Function using (_$_)
open import Proposition.Function
  renaming (_$_ to _$'_) using ()
open import Function.Property

-- is-finite : (X : 𝒰 ˙) → 𝒰 ᵖ
-- is-finite X = ∃ λ (n : ℕ) → ∃ λ (f : (x : X) → Finℕ n) → Bijective f

-- list-of-Finℕ-fun : ∀ {n} → ∃Bijective (Vec X n) ((a : Finℕ n) → X)
-- list-of-Finℕ-fun {n = n} = {!!}
--   where fun : (vec : Vec X n) (a : Finℕ n) → X
--         fun vec a = vec ! toℕ a [ toℕ< a ]
--         instance
--           Surjective-fun : Surjective fun
--           surj ⦃ Surjective-fun ⦄ y = {!!} , {!!}
--           Injective-fun : Injective fun
--           inj ⦃ Injective-fun ⦄ {[]} {[]} p = refl []
--           inj ⦃ Injective-fun ⦄ {h1 ∷ t1} {h2 ∷ t2} p =
--             ⟵ Vec== ((ap (_$ 0) p) , {!!})

-- finite-can-be-enumerated : is-finite X ↔ ∃ λ n → ∃ λ (l : Vec X n) → ∀ x → x ∈ l
-- ⟶ finite-can-be-enumerated (n , (f , f-def)) = {!!} , {!!}
-- ⟵ finite-can-be-enumerated = {!!}

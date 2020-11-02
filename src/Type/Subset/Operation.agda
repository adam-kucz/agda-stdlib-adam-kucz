{-# OPTIONS --exact-split --safe #-}
module Type.Subset.Operation where

open import Type.Subset.Definition hiding (_∪_; ⋃_; _∩_; ⋂_)

open import Universes
open import Logic

module General where

  open import Type.BinarySum
  
  infixl 105 _∪_
  _∪_ : (A : Subset 𝒰 X)(B : Subset 𝒱 Y) → Subset (𝒰 ⊔ 𝒱) (X + Y)
  _∪_ {𝒱 = 𝒱} A B (inl x) = Lift𝒰 {𝒱 = 𝒱} (x ∈ A)
  _∪_ {𝒰 = 𝒰} A B (inr y) = Lift𝒰 {𝒱 = 𝒰} (y ∈ B)

module SamePowerset where

  infixl 105 _∪_
  _∪_ : (A B : Subset 𝒰 X) → Subset 𝒰 X
  (A ∪ B) x = x ∈ A ∨ x ∈ B

infixr 108 ⋃_
⋃_ : {X : 𝒰 ˙}(U : Subset 𝒱 (Subset 𝒲 X)) → Subset (𝒰 ⊔ 𝒱 ⊔ 𝒲 ⁺) X
⋃_ {𝒲 = 𝒲}{X = X} U x = ∃ λ (S : Subset 𝒲 X) → S ∈ U ∧ x ∈ S

open import Type.Identity

infixl 104 _∩_
_∩_ : (A : Subset 𝒰 X)(B : Subset 𝒱 X) → Subset (𝒰 ⊔ 𝒱) X
(A ∩ B) x = x ∈ A ∧ x ∈ B

infixl 108 ⋂_
⋂_ : {X : 𝒰 ˙}(U : Subset 𝒱 (Subset 𝒲 X)) → Subset (𝒰 ⊔ 𝒱 ⊔ 𝒲 ⁺) X
⋂_ {𝒲 = 𝒲}{X = X} U x = ∀ (S : Subset 𝒲 X)(p : S ∈ U) → x ∈ S

infixr 105 _`_
_`_ : {X : 𝒰 ˙}{Y : 𝒱 ˙}
  (f : X → Y)
  (S : Subset 𝒲 X)
  → ----------------
  Subset (𝒰 ⊔ 𝒱 ⊔ 𝒲) Y
(f ` S) y = ∃ λ x → f x == y ∧ x ∈ S

infix 105 _⁻¹`_
_⁻¹`_ :
  (f : X → Y)
  (S : Subset 𝒰 Y)
  → ----------------
  Subset 𝒰 X
(f ⁻¹` S) x = f x ∈ S

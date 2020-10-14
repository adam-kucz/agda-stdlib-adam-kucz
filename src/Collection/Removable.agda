{-# OPTIONS --exact-split --safe #-}
module Collection.Removable where

open import Collection.Definition

open import Universes
open import Type.Identity
open import Logic
open import Data.List.Definition
open import Data.List.Collection

record Removable
    (Col : 𝒱 ˙)
    (Elem : 𝒰 ˙)
    ⦃ col : Collection 𝒲 Col Elem ⦄
    : ------------------------
    𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒲 ˙
    where
  field
    remove : (x : Elem) (S : Col) → Col
    remove-valid :
      {x y : Elem} {S : Col}
      → ------------------------------
      x ∈ remove y S ↔ x ∈ S ∧ x ≠ y

  remove-all : (l : List Elem) (S : Col) → Col
  remove-all [] S = S
  remove-all (h ∷ l) S = remove h (remove-all l S)

  remove-all-prop :
    {x : Elem} {l : List Elem} {S : Col}
    → ------------------------------------
    x ∈ remove-all l S ↔ x ∈ S ∧ x ∉ l
  ⟶ (remove-all-prop {l = []}) p = p , λ ()
  ⟶ (remove-all-prop {l = _ ∷ _}) p with ⟶ remove-valid p
  ⟶ (remove-all-prop {x = x}{h ∷ l}{S}) p | q , x≠h =
    ∧left ih ,
    λ { (x∈x∷ _) → x≠h (refl _)
      ; (x∈tail _ x∈l) → ∧right ih x∈l }
    where ih : x ∈ S ∧ x ∉ l
          ih = ⟶ (remove-all-prop {l = l}) q
  ⟵ (remove-all-prop {l = []}) (x∈S , _) = x∈S
  ⟵ (remove-all-prop {l = h ∷ l}) (x∈S , x∉h∷l) =
    ⟵ remove-valid (
      ⟵ (remove-all-prop {l = l}) (x∈S , λ x∈l → x∉h∷l (x∈tail h x∈l)) ,
      λ { (refl x) → x∉h∷l (x∈x∷ l) }
      )

  _∉remove_ : (x : Elem)(S : Col) → x ∉ remove x S
  (x ∉remove S) q = ∧right (⟶ remove-valid q) (refl x)

open Removable ⦃ … ⦄ public

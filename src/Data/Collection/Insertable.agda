{-# OPTIONS --exact-split --prop --safe #-}
module Data.Collection.Insertable where

open import Data.Collection.Definition

open import PropUniverses
open import Data.List.Definition
open import Data.List.Collection
open import Proposition.Identity
open import Logic

record Insertable
    (Col : 𝒱 ˙)
    (Elem : 𝒰 ˙)
    ⦃ col : Collection 𝒲 Col Elem ⦄
    : ------------------------
    𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒲 ˙
    where
  field
    insert : (x : Elem) (S : Col) → Col
    insert-valid :
      {x y : Elem}
      {S : Col}
      → ------------------------------
      y ∈ insert x S ↔ y ∈ S ∨ x == y

  extend : (l : List Elem) (S : Col) → Col
  extend [] S = S
  extend (h ∷ l) S = insert h (extend l S)

  extend-prop :
    {x : Elem} {l : List Elem} {S : Col}
    → --------------------
    x ∈ extend l S ↔ x ∈ l ∨ x ∈ S
  ⟶ (extend-prop {l = []}) p = ∨right p
  ⟶ (extend-prop {l = _ ∷ _}) p
    with ⟶ insert-valid p
  ⟶ (extend-prop {l = h ∷ l}) p | ∨left q
    with ⟶ (extend-prop {l = l}) q
  ⟶ (extend-prop {x = _} {h ∷ l}) p | _ | ∨left q = ∨left (x∈tail h q)
  ⟶ (extend-prop {x = _} {h ∷ l}) p | _ | ∨right q = ∨right q
  ⟶ (extend-prop {l = x ∷ l}) p | ∨right (refl x) = ∨left (x∈x∷ l)
  ⟵ (extend-prop {l = h ∷ l}) (∨left (x∈x∷ l)) =
    ⟵ insert-valid (∨right (refl h))
  ⟵ (extend-prop {l = _ ∷ l}) (∨left (x∈tail _ p)) =
    ⟵ insert-valid (∨left (⟵ extend-prop (∨left p)))
  ⟵ (extend-prop {l = []}) (∨right q) = q
  ⟵ (extend-prop {l = _ ∷ l}) (∨right q) =
    ⟵ insert-valid (∨left (⟵ (extend-prop {l = l}) (∨right q)))

open Insertable ⦃ … ⦄ public

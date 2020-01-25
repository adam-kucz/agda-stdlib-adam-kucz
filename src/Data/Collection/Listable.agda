{-# OPTIONS --exact-split --prop --safe #-}
module Data.Collection.Listable where

open import Data.Collection.Definition
open import Data.Collection.Insertable

open import PropUniverses
open import Logic
open import Data.List.Definition
open import Data.List.Collection

record Listable 𝒲 (Col : 𝒱 ˙) (Elem : 𝒰 ˙) : 𝒰 ⁺ ⊔ 𝒱 ⁺ ⊔ 𝒲 ⁺ ˙ where
  field
    ⦃ collection ⦄ : Collection 𝒲 Col Elem
    to-list : (S : Col) → List Elem
    to-list-valid :
      {S : Col} {x : Elem}
      → --------------------
      x ∈ S ↔ x ∈ to-list S
    
open Listable ⦃ … ⦄ public

infixl 105 _++_
_++_ :
  {Elem : 𝒰 ˙} {Col : 𝒱 ˙}
  ⦃ _ : Listable 𝒲 Col Elem ⦄
  ⦃ _ : Insertable Col Elem ⦄
  → ----------------------
  (l l' : Col) → Col
l ++ l' = extend (to-list l') l

++-prop : 
  {Elem : 𝒰 ˙} {Col : 𝒱 ˙}
  ⦃ _ : Listable 𝒲 Col Elem ⦄
  ⦃ _ : Insertable Col Elem ⦄
  {x : Elem}
  {l l' : Col}
  → -----------------------
  x ∈ l ++ l' ↔ x ∈ l ∨ x ∈ l'
⟶ (++-prop {l' = l'}) p with ⟶ (extend-prop {l = to-list l'}) p
⟶ ++-prop _ | ∨left q = ∨right (⟵ to-list-valid q)
⟶ ++-prop _ | ∨right q = ∨left q
⟵ (++-prop {l' = l'}) (∨left p) =
  ⟵ (extend-prop {l = to-list l'}) (∨right p)
⟵ ++-prop (∨right q) = ⟵ extend-prop (∨left (⟶ to-list-valid q))

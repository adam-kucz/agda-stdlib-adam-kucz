{-# OPTIONS --exact-split --prop --safe #-}
module Collection.Listable.Definition where

open import Collection.Definition
open import Collection.Insertable

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

pure-listable :{Col : 𝒱 ˙}{Elem : 𝒰 ˙}
  (tl : (S : Col) → List Elem)
  → --------------------------------------------------
  Listable 𝒰₀ Col Elem
to-list ⦃ pure-listable tl ⦄ = tl
_∈_ ⦃ collection ⦃ pure-listable tl ⦄ ⦄ x c = x ∈ tl c
⟶ (to-list-valid ⦃ pure-listable tl ⦄) p = p
⟵ (to-list-valid ⦃ pure-listable tl ⦄) p = p

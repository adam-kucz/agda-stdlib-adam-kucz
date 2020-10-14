{-# OPTIONS --exact-split --safe #-}
module Collection.Operation.Function where

open import Collection.Operation.Definition

open import Universes
open import Data.List.Definition
open import Collection.Definition
open import Collection.Basic
open import Collection.Listable

infixr 108 ⋃_
⋃' : {Col : 𝒱 ˙}{Elem : 𝒰 ˙}{Col' : 𝒯 ˙}
  ⦃ col : Collection 𝒲 Col Elem ⦄
  ⦃ un : Union Col Elem ⦄
  ⦃ ls' : Listable 𝒳 Col' Col ⦄
  (S : Col')
  (s : Col)
  → -------------------------------
  Col
⋃' S s = foldr _∪_ s S
⋃_ : {Col : 𝒱 ˙}{Elem : 𝒰 ˙}{Col' : 𝒯 ˙}
  ⦃ col : Collection 𝒲 Col Elem ⦄
  ⦃ em : Empty Col Elem ⦄
  ⦃ un : Union Col Elem ⦄
  ⦃ ls' : Listable 𝒳 Col' Col ⦄
  (S : Col')
  → -------------------------------
  Col
⋃ S = ⋃' S ∅

infixl 108 ⋂_
⋂' : {Col : 𝒱 ˙}{Elem : 𝒰 ˙}{Col' : 𝒯 ˙}
  ⦃ col : Collection 𝒲 Col Elem ⦄
  ⦃ un : Intersection Col Elem ⦄
  ⦃ ls' : Listable 𝒳 Col' Col ⦄
  (S : Col')
  (s : Col)
  → -------------------------------
  Col
⋂' S s = foldr _∩_ s S
⋂_ :
  {Col : 𝒱 ˙}
  {Elem : 𝒰 ˙}
  {Col' : 𝒯 ˙}
  ⦃ col : Collection 𝒲 Col Elem ⦄
  ⦃ univ : Universal Col Elem ⦄
  ⦃ inter : Intersection Col Elem ⦄
  ⦃ ls' : Listable 𝒳 Col' Col ⦄
  (S : Col')
  → -------------------------------
  Col
⋂ S = ⋂' S Univ

open import Collection.Insertable
open import Collection.Removable

from-list-uniq :
  {Col : 𝒱 ˙}
  {Elem : 𝒰 ˙}
  ⦃ ls : Listable 𝒳 Col Elem ⦄
  ⦃ ins : Insertable Col Elem ⦄
  ⦃ rem : Removable Col Elem ⦄
  (S : Col)
  (l : List Elem)
  → --------------------------
  Col
from-list-uniq S [] = S
from-list-uniq S (h ∷ t) =
  insert h (remove h (from-list-uniq S t))

recreate :
  {Col : 𝒱 ˙}
  {Elem : 𝒰 ˙}
  ⦃ ls : Listable 𝒳 Col Elem ⦄
  ⦃ ins : Insertable Col Elem ⦄
  ⦃ rem : Removable Col Elem ⦄
  (S : Col)
  → -------------------------------
  Col
recreate S = from-list-uniq S (to-list S)

open import Type.Decidable
open import Logic
open import Proof
open import Data.List.Collection

recreate-prop :
  {Col : 𝒱 ˙}
  {Elem : 𝒰 ˙}
  ⦃ ls : Listable 𝒳 Col Elem ⦄
  ⦃ ins : Insertable Col Elem ⦄
  ⦃ rem : Removable Col Elem ⦄
  ⦃ eq-dec : HasDecidableIdentity Elem ⦄
  {x : Elem}
  {S : Col}
  → ------------------------------
  x ∈ recreate S ↔ x ∈ S
⟵ (recreate-prop {S = S}) p with to-list S | ⟶ to-list-valid p
⟵ (recreate-prop {Elem = Elem}{x = x}{S}) p | l | q = go l q
  where go :
          (l : List Elem)
          (q : x ∈ l)
          → --------------------
          x ∈ from-list-uniq S l
        go (h ∷ t) (x∈x∷ t) = ⟵ insert-valid $ ∨right (Id.refl h)
        go (h ∷ t) (x∈tail h q) with decide (x == h)
        go (h ∷ t) (x∈tail h q) | true (Id.refl h) =
          ⟵ insert-valid $ ∨right (Id.refl h)
        go (h ∷ t) (x∈tail h q) | false ¬p =
          ⟵ insert-valid $ ∨left $ ⟵ remove-valid (go t q , ¬p)
⟶ (recreate-prop ⦃ ls = ls ⦄{x = x}{S}) p with ⟵ (to-list-valid ⦃ ls ⦄ {S}{x})
⟶ (recreate-prop ⦃ ls = ls ⦄{S = S}) p | q with to-list ⦃ ls ⦄ S
⟶ (recreate-prop {Elem = Elem}{x = x}{S}) p | q | l = go l q p
  where go :
          (l : List Elem)
          (q : x ∈ l → x ∈ S)
          (p : x ∈ from-list-uniq S l)
          → --------------------------
          x ∈ S
        go [] _ p = p
        go (h ∷ t) q p with ⟶ insert-valid p
        go (h ∷ t) q p | ∨right (Id.refl h) = q $ x∈x∷ t 
        go (h ∷ t) q p | ∨left r =
          go t (λ p' → q $ x∈tail h p') (∧left $ ⟶ remove-valid r)

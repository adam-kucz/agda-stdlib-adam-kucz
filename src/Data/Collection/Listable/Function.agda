{-# OPTIONS --exact-split --prop #-}
module Data.Collection.Listable.Function where

open import Data.Collection.Listable.Definition

open import Universes
open import Data.Collection.Insertable
open import Data.Collection.Definition

infixl 105 _++_
_++_ :
  {Elem : 𝒰 ˙} {Col : 𝒱 ˙}
  ⦃ _ : Listable 𝒲 Col Elem ⦄
  ⦃ _ : Insertable Col Elem ⦄
  → ----------------------
  (l l' : Col) → Col
l ++ l' = extend (to-list l') l

open import Logic

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

open import Structure.Monoid
open import Data.Functor
open import Data.List.Functor

fold-map : {Col : 𝒰 ˙}{Elem : 𝒱 ˙}
  ⦃ list : Listable 𝒲 Col Elem ⦄
  (f : Elem → X)
  ⦃ mon : Monoid X ⦄
  (S : Col)
  → ---------------------------
  X
fold-map f S = mconcat (fmap f (to-list S))

open import Function

fold : {Col : 𝒰 ˙}{Elem : 𝒱 ˙}
  ⦃ list : Listable 𝒲 Col Elem ⦄
  ⦃ mon : Monoid Elem ⦄
  (S : Col)
  → ---------------------------
  Elem
fold = fold-map id

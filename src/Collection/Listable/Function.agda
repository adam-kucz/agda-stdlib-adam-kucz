{-# OPTIONS --exact-split --safe #-}
module Collection.Listable.Function where

open import Collection.Listable.Definition

open import Universes
open import Collection.Insertable
open import Collection.Definition

infixl 105 _++_
_++_ :
  {Elem : 𝒰 ˙} {Col : 𝒱 ˙}
  ⦃ _ : Listable 𝒲 Col Elem ⦄
  ⦃ _ : Insertable Col Elem ⦄
  → ----------------------
  (l l' : Col) → Col
l ++ l' = extend (to-list l') l

open import Logic hiding (⊥-recursion)

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
open import Data.List.Operation.Basic

fold-map : {Col : 𝒰 ˙}{Elem : 𝒱 ˙}
  ⦃ list : Listable 𝒲 Col Elem ⦄
  (f : Elem → X)
  ⦃ mon : Monoid X ⦄
  (S : Col)
  → ---------------------------
  X
fold-map f S = mconcat (map f (to-list S))

open import Function

fold : {Col : 𝒰 ˙}{Elem : 𝒱 ˙}
  ⦃ list : Listable 𝒲 Col Elem ⦄
  ⦃ mon : Monoid Elem ⦄
  (S : Col)
  → ---------------------------
  Elem
fold = fold-map id

foldr : {Col : 𝒰 ˙}{Elem : 𝒱 ˙}
  ⦃ list : Listable 𝒲 Col Elem ⦄
  (f : (e : Elem)(rest : X) → X)
  (z : X)
  (S : Col)
  → ---------------------------
  X
foldr f = flip (fold-map f)
  where instance _ = EndofunctionMonoid

foldl : {Col : 𝒰 ˙}{Elem : 𝒱 ˙}
  ⦃ list : Listable 𝒲 Col Elem ⦄
  (f : (sofar : X)(e : Elem) → X)
  (z : X)
  (S : Col)
  → ---------------------------
  X
foldl f = flip (fold-map (flip f))
  where instance _ = dual EndofunctionMonoid

open import Data.Nat

len :
  {Col : 𝒰 ˙}{Elem : 𝒱 ˙}
  ⦃ list : Listable 𝒲 Col Elem ⦄
  (S : Col)
  → ---------------------------
  ℕ
len = fold-map (λ _ → 1) ⦃ Monoid+ ⦄

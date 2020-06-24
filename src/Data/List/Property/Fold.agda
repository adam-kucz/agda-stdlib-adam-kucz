{-# OPTIONS --exact-split --prop --safe #-}
module Data.List.Property.Fold where

open import Data.List.Definition
open import Data.List.Collection
open import Data.List.Operation.Basic
open import Data.List.Property.Instance

open import Universes
open import Data.Nat
open import Collection hiding (_++_)
open import Proof

open import Structure.Monoid

fold-map++ : ∀(f : X → Y)⦃ mon : Monoid Y ⦄ l₀ l₁
  → --------------------------------------------------------
  fold-map f (l₀ ++ l₁) == fold-map f l₀ ∙ fold-map f l₁
fold-map++ f l₀ l₁ =
  proof fold-map f (l₀ ++ l₁)
    === mconcat (map f l₀ ++ map f l₁) :by: ap mconcat $ map++ l₀ l₁ f
    === fold-map f l₀ ∙ fold-map f l₁  :by: mconcat-∪ (map f l₀) (map f l₁)
  qed

len-map : ∀(f : X → Y) l
  → ----------------------------------------
  len (map f l) == len l
len-map f [] = Id.refl 0
len-map f (h ∷ t) = ap suc $ len-map f t


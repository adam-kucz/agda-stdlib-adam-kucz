{-# OPTIONS --exact-split --safe --prop #-}
open import Universes
open import Structure.Monoid.Definition

module Structure.Monoid.Function
  {X : 𝒰 ˙}
  ⦃ M : Monoid X ⦄
  where

open import Operation.Binary
open import Data.List.Definition
open import Data.List.Operation
open import Proof

mconcat : (l : List X) → X
mconcat [] = e
mconcat (h ∷ l) = h ∙ mconcat l

mconcat-++ : ∀ l l'
  → ----------------------------------------
  mconcat (l ++ l') == mconcat l ∙ mconcat l'
mconcat-++ [] l' = sym $ left-unit (mconcat l')
mconcat-++ (h ∷ l) l' =
  proof h ∙ mconcat (l ++ l')
    === h ∙ (mconcat l ∙ mconcat l')
      :by: ap (h ∙_) $ mconcat-++ l l'
    === h ∙ mconcat l ∙ mconcat l'
      :by: assoc h _ _
  qed


{-# OPTIONS --exact-split --safe #-}
module Structure.Semigroup.Function where

open import Structure.Semigroup.Definition

open import Universes

open import Data.NonemptyList
open import Logic
  
module WithSemigroup {X : 𝒰 ˙}⦃ sem : Semigroup X ⦄ where

  open import Proof

  semconcat : (l : NonemptyList X) → X
  semconcat [ h ] = h
  semconcat (h ∷ t) = h ∙ semconcat t

  open import Collection
  open import Operation.Binary

  semconcat-∪ : ∀ l l'
    → ----------------------------------------
    semconcat (l ∪ l') == semconcat l ∙ semconcat l'
  semconcat-∪ [ x ] l' = refl (x ∙ semconcat l')
  semconcat-∪ (h ∷ t) l' =
    proof h ∙ semconcat (t ∪ l')
      === h ∙ (semconcat t ∙ semconcat l')
        :by: ap (h ∙_) $ semconcat-∪ t l'
      === h ∙ semconcat t ∙ semconcat l'
        :by: assoc h _ _
    qed

open WithSemigroup public

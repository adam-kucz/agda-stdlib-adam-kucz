{-# OPTIONS --exact-split --safe --prop #-}
module Structure.Monoid.Function where

open import Structure.Monoid.Definition

open import Universes
open import Data.Collection
open import Data.List.Definition
open import Data.List.Collection

module WithMonoid {X : 𝒰 ˙}⦃ M : Monoid X ⦄ where

  open import Operation.Binary
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
  
  open import Relation.Binary
  
  mconcat-preserv :
    {_≤_ : Rel 𝒰 X X}
    ⦃ _ : Transitive _≤_ ⦄
    (p₀ : ∀ x y → x ≤ x ∙ y)
    (p₁ : ∀ x y → y ≤ x ∙ y)
    → --------------------------------
    ∀ l x (p : x ∈ l) → x ≤ mconcat l
  mconcat-preserv p₀ p₁ (x ∷ t) x (x∈x∷ t) = p₀ x (mconcat t)
  mconcat-preserv {_≤_ = _≤_} p₀ p₁ (h ∷ t) x (x∈tail h p) =
    proof x
      〉 _≤_ 〉 mconcat t
        :by: mconcat-preserv p₀ p₁ t x p
      〉 _≤_ 〉 h ∙ mconcat t
        :by: p₁ h (mconcat t)
    qed
    where open TransMakeComposable _≤_

open WithMonoid public

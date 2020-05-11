{-# OPTIONS --exact-split --safe --prop #-}
module Structure.Monoid.Function where

open import Structure.Monoid.Definition

open import Universes
open import Collection.Definition
open import Collection.Operation.Definition
open import Data.List.Definition
open import Data.List.Collection
open import Data.List.Property

module WithMonoid {X : 𝒰 ˙}⦃ M : Monoid X ⦄ where

  open import Operation.Binary
  open import Data.List.Operation.Basic
  open import Proof
  
  mconcat : (l : List X) → X
  mconcat [] = e
  mconcat (h ∷ l) = h ∙ mconcat l
  
  mconcat-∪ : (l l' : List X)
    → ----------------------------------------
    mconcat (l ∪ l') == mconcat l ∙ mconcat l'
  mconcat-∪ [] l' = sym $ left-unit (mconcat l')
  mconcat-∪ (h ∷ l) l' =
    proof h ∙ mconcat (l ++ l')
      === h ∙ (mconcat l ∙ mconcat l')
        :by: ap (h ∙_) $ mconcat-∪ l l'
      === h ∙ mconcat l ∙ mconcat l'
        :by: assoc h _ _
    qed
  
  open import Relation.Binary
  
  mconcat-preserv :
    {R : Rel 𝒰 X X}
    → let _≤_ = R in
    ⦃ _ : Transitive _≤_ ⦄
    (p₀ : ∀ x y → x ≤ x ∙ y)
    (p₁ : ∀ x y → y ≤ x ∙ y)
    → --------------------------------
    ∀ l x (p : x ∈ l) → x ≤ mconcat l
  mconcat-preserv p₀ p₁ (x ∷ t) x (x∈x∷ t) = p₀ x (mconcat t)
  mconcat-preserv {R = _≤_} p₀ p₁ (h ∷ t) x (x∈tail h p) =
    proof x
      〉 _≤_ 〉 mconcat t
        :by: mconcat-preserv p₀ p₁ t x p
      〉 _≤_ 〉 h ∙ mconcat t
        :by: p₁ h (mconcat t)
    qed
    where open MakeTransComposable _≤_

open WithMonoid public


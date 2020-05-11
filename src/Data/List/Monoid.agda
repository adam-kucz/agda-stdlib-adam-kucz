{-# OPTIONS --exact-split --safe --prop #-}
module Data.List.Monoid where

open import Data.List.Definition
open import Data.List.Operation.Basic
open import Structure.Monoid.Definition

open import Universes
open import Operation.Binary
open import Proof

instance
  ListMonoid : Monoid (List X)
_∙_ ⦃ ListMonoid ⦄ = _++_
e ⦃ ListMonoid ⦄ = []

distrib-++ : (f : List X → List Y)
  (p : f [] == [] {X = Y})
  (q : ∀ h t → f (h ∷ t) == f [ h ] ++ f t)
  → --------------------------------------
  ∀ l l' → f (l ++ l') == f l ++ f l'
distrib-++ f p q [] l' = ap (_++ f l') $ sym p
distrib-++ f p q (h ∷ l) l' =
  proof f (h ∷ (l ++ l'))
    === f [ h ] ++ f (l ++ l')
      :by: q h (l ++ l')
    === f [ h ] ++ (f l ++ f l')
      :by: ap (f [ h ] ++_) $ distrib-++ f p q l l'
    === f [ h ] ++ f l ++ f l'
      :by: assoc _ (f l) (f l')
    === f (h ∷ l) ++ f l'
      :by: ap (_++ f l') $ sym $ q h l
  qed

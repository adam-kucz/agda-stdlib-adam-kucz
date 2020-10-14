{-# OPTIONS --safe --exact-split  #-}
module Type.Permutation.Property where

open import Type.Permutation.Definition as Perm
open import Type.Permutation.Class

open import Universes
open import Data.List.Definition
open import Data.List.Collection
open import Collection.Definition hiding (_⊆_)
open import Relation.Binary as Rel
  renaming (refl-trans-close to rtc) hiding (_~_)
open import Logic
open import Proof
open import Logic.Proof

∈-~ : ∀ (x : X){l l'}(p : l ~ l')
  → -------------------------
  x ∈ l ↔ x ∈ l'
∈-~ x p = go p , go $ sym p
  where go : ∀ {l l'}(p : l ~ l')(q : x ∈ l) → x ∈ l'
        ∈-single-swap : ∀ {l l'}
          (p : single-swap l l')
          (q : x ∈ l)
          → ------------------------------
          x ∈ l'
        ∈-single-swap (swap x y l) (x∈x∷ y ∷ l) = x∈tail y (x∈x∷ l)
        ∈-single-swap (swap x y l) (x∈tail x (x∈x∷ l)) = x∈x∷ (x ∷ l)
        ∈-single-swap (swap x y l) (x∈tail x (x∈tail y q)) =
          x∈tail y $ x∈tail x q
        ∈-single-swap (step {l₁ = l₁} x p) (x∈x∷ t) = x∈x∷ l₁
        ∈-single-swap (step x p) (x∈tail x q) =
          x∈tail x $ ∈-single-swap p q
        go (rfl a) q = q
        go (step aRb p) q = go p $ ∈-single-swap aRb q

open import Data.List.Property.Instance
open import Data.List.Monoid
open import Structure.Monoid
open import Operation.Binary
open import Collection.Listable.Function
open import Function.Proof

instance
  Relating-fold-f-single-swap-== : {M : 𝒰 ˙}
    {f : X → M}
    ⦃ mon : Monoid M ⦄
    ⦃ com : Commutative (_∙_ ⦃ mon ⦄) ⦄
    → ----------------------------------
    Relating (fold-map f) single-swap _==_
  Relating-fold-f-~-== : {M : 𝒰 ˙}
    {f : X → M}
    ⦃ mon : Monoid M ⦄
    ⦃ com : Commutative (_∙_ ⦃ mon ⦄) ⦄
    → ----------------------------------
    Relating (fold-map f) _~_ _==_

rel-preserv ⦃ Relating-fold-f-single-swap-== {f = f} ⦄
  (swap x y l) =
    proof f x ∙ (f y ∙ fold-map f l)
      === f x ∙ f y ∙ fold-map f l   :by: assoc (f x) (f y) _
      === f y ∙ f x ∙ fold-map f l
        :by: ap (_∙ fold-map f l) $ comm (f x) (f y)
      === f y ∙ (f x ∙ fold-map f l) :by: sym $ assoc (f y) (f x) _
    qed
rel-preserv ⦃ Relating-fold-f-single-swap-== {f = f} ⦄
  (step x l-ss-l') =
    ap (f x ∙_) $
    rel-preserv ⦃ Relating-fold-f-single-swap-== ⦄ l-ss-l'

module Transferred {X : 𝒰 ˙} where
  open import
    Relation.Binary.ReflexiveTransitiveClosure.Transfer
      (_~_ {X = X}) single-swap ⦃ refl _ ⦄
    public

open import Relation.Binary.Proof

Relating-fold-f-~-== = Transferred.InheritsRelatingR
  where instance
          ==⊆rtc-== : rtc (_==_ {X = X}) ⊆ _==_
          _ = Id⊆rtc-empty
        ==⊆rtc-== {X = X} =
          proof rtc _==_
            〉 _⊆_ 〉 rtc (rtc (empty-rel X X))
              :by: Subrelation-2-Subrelation-rtc {R = _==_}   [: _⊆_ ]
            〉 _⊆_ 〉 rtc (empty-rel X X) :by: Subrelation-rtc2 [: _⊆_ ]
            〉 _⊆_ 〉 _==_                :by: rtc-empty⊆Id
          qed

open import Data.Nat

empty~ : {l : List X}
  (p : [] ~ l) → l == []
empty~ (rfl []) = refl []

singleton~ : ∀ {x : X}{l}
  (p : [ x ] ~ l)
  → -----------------------
  l == [ x ]
singleton~ (rfl [ x ]) = refl [ x ]
singleton~ (step (step _ ()) _)

{-# OPTIONS --exact-split --prop #-}
module Data.FinMultiset where

open import PropUniverses
open import Proposition.Sum
import Relation.Binary
open import Data.List
open import Proposition.Permutation hiding (refl)
open import Type.Quotient.Independent

module ListQuot {𝒰} (X : 𝒰 ˙) = Quotient (List X) _~_

FinMultiset : (X : 𝒰 ˙) → 𝒰 ⁺ ˙
FinMultiset X = ListQuot.Type X
  
∅ : FinMultiset X
∅ {X = X} = ListQuot.class-of X []
  
singleton : (x : X) → FinMultiset X
singleton {X = X} x = ListQuot.class-of X [ x ]

fromList : (l : List X) → FinMultiset X
fromList {X = X} = ListQuot.class-of X

open import Collection
open import Proposition.Identity hiding (refl)
open import Logic
open import Axiom.PropositionExtensionality

open import Proof
open import Proposition.Permutation.Proof

private
  from-prop== : (p : 𝑋 == 𝑌) (q : 𝑋) → 𝑌

from-prop== = {!!}

instance
  FinMultisetCollection : {X : 𝒰 ˙} → Collection 𝒰 (FinMultiset X) X
  FinMultisetInsertable : Insertable (FinMultiset X) X

_∈_ ⦃ FinMultisetCollection ⦄ x (p , _) = ∃ λ l → p l ∧ x ∈ l

insert ⦃ FinMultisetInsertable {𝒰}{X} ⦄ x (p , is-class) =
  cond , get is-class
  where cond : (l : List X) → 𝒰 ᵖ
        cond l = ∃ λ l' → p l' ∧ l ~ insert x l'
        get :
          (prev : ∃ λ l → ∀ l' → p l' == l ~ l')
          → ----------------------------------------
          ∃ λ l → ∀ l' → cond l' == l ~ l'
        get (l , is-class) = x ∷ l , λ l' → prop-ext (
          (λ { (l'' , (pl'' , perm)) →
              proof x ∷ l
                〉 _~_ 〉 x ∷ l''
                  :by: step x $ from-prop== (is-class l'') pl''
                〉 _~_ 〉 l'
                  :by: sym perm
              qed}) ,
          λ q → l ,
            (from-prop== (sym $ is-class l) (refl l) , sym q))
          
⟶ (insert-valid ⦃ FinMultisetInsertable ⦄) p = {!!}
⟵ (insert-valid ⦃ FinMultisetInsertable ⦄) q = {!!}

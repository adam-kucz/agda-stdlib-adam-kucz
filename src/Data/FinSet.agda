{-# OPTIONS --exact-split --prop #-}
module Data.FinSet where

open import PropUniverses
open import Proposition.Sum
import Relation.Binary
open import Data.List
open import Proposition.Permutation using (_~_)
open import Proposition.Permutation.Multi hiding (refl)
open import Type.Quotient
  
module ListQuot {𝒰} (X : 𝒰 ˙) = Quotient (List X) _~~_

FinSet : (X : 𝒰 ˙) → 𝒰 ⁺ ˙
FinSet X = ListQuot.Type X
  
∅ : FinSet X
∅ {X = X} = ListQuot.class-of X []
  
singleton : (x : X) → FinSet X
singleton {X = X} x = ListQuot.class-of X [ x ]

fromList : (l : List X) → FinSet X
fromList {X = X} = ListQuot.class-of X
  
open import Collection
open import Proposition.Identity hiding (refl)
open import Logic
open import Axiom.PropositionExtensionality

open import Proof
open import Proposition.Permutation.Proof

private
  from-prop== : (p : 𝑋 == 𝑌) (q : 𝑋) → 𝑌
  from-prop== = Id.subst (λ x → x)

instance
  FinSetCollection : {X : 𝒰 ˙} → Collection 𝒰 (FinSet X) X
  _∈_ ⦃ FinSetCollection ⦄ x (p , _) = ∃ λ l → p l ∧ x ∈ l

  FinSetInsertable : Insertable (FinSet X) X
  insert ⦃ FinSetInsertable {𝒰}{X} ⦄ x S =
    p' S , q' S
    where p' : (S : FinSet X)(l : List X) → 𝒰 ᵖ
          p' (p , _) l = ∃ λ l' → p l' ∧ x ∷ l' ~~ l
          q' : (S : FinSet X) → ∃ λ l → (l' : List X) → p' S l' == l ~~ l'
          q' (p , (l , p')) = x ∷ l , λ l' → prop-ext (
            (λ { (t , (pt , x∷t~~l')) →
              proof x ∷ l
                〉 _~~_ 〉 x ∷ t :by: step x (Id.coe (p' t) pt)
                〉 _~~_ 〉 l'     :by: x∷t~~l'
              qed}) ,
            λ q → l , (Id.coe (sym $ p' l) (refl l) , q))
  ⟶ (insert-valid ⦃ FinSetInsertable ⦄ {x}{y}{p , q})
    (l , (l' , (pl' , x∷l'~~l) , y∈l)) = go
    where go : ∃ (λ l₁ → p l₁ ∧ member y l₁) ∨ x == y
          go = {!!}
  ⟵ (insert-valid ⦃ FinSetInsertable ⦄) (∨left (elem₁ , (left₁ , right₁))) = {!!}
  ⟵ (insert-valid ⦃ FinSetInsertable ⦄) (∨right (Idₚ.refl x)) = {!!}

  FinSetRemovable : Removable (FinSet X) X
  -- insert ⦃ FinSetInsertable {𝒰} ⦄ {X} x (p , is-class) =
  --   cond , get is-class
  --   where cond : (l : List X) → 𝒰 ᵖ
  --         cond l = ∃ λ l' → p l' ∧ l ~~ insert x l'
  --         get :
  --           (prev : ∃ λ l → ∀ l' → p l' == l ~~ l')
  --           → ----------------------------------------
  --           ∃ λ l → ∀ l' → cond l' == l ~~ l'
  --         get (l , is-class) = x ∷ l , λ l' → prop-ext (
  --           (λ { (l'' , (pl'' , perm)) →
  --               proof x ∷ l
  --                 〉 _~~_ 〉 x ∷ l''
  --                   :by: step x $ from-prop== (is-class l'') pl''
  --                 〉 _~~_ 〉 l'
  --                   :by: sym perm
  --               qed}) ,
  --           λ q → l ,
  --             (from-prop== (sym $ is-class l) (refl l) , sym q))
  -- ⟶ (insert-valid ⦃ FinSetInsertable ⦄ {S = p , is-class})
  --   (l , (l' , (pl' , l~~x∷l') , y∈l)) = {!!}
  -- ⟵ (insert-valid ⦃ FinSetInsertable ⦄) q = {!!}

{-# OPTIONS --exact-split --prop --safe #-}
module Collection.Listable.Property where

open import Collection.Definition
open import Collection.Listable.Definition

open import Universes
import Proposition.Permutation as Perm
import Proposition.Permutation.Class as PermClass
open import Relation.Binary
  hiding (_~_; Reflexive~; Transitive~; Symmetric~)

module WithListable
    {Col : 𝒰 ˙}
    {Elem : 𝒱 ˙}
    ⦃ lst : Listable 𝒲 Col Elem ⦄
    where

  _~_ : BinRel 𝒱 Col
  x ~ y = to-list x Perm.~ to-list y

  instance
    Reflexive~ : Reflexive _~_
    Transitive~ : Transitive _~_
    Symmetric~ : Symmetric _~_
  
  refl ⦃ Reflexive~ ⦄ x = refl ⦃ PermClass.Reflexive-rtc ⦄ (to-list x)
  trans ⦃ Transitive~ ⦄ = trans ⦃ PermClass.Transitive-rtc ⦄
  sym ⦃ Symmetric~ ⦄ = sym ⦃ PermClass.InheritsSymmetric-rtc ⦄

  open import Logic
  open import Proof
  open import Logic.Proof
  open import Data.List

  ∈-~ : ∀ (x : Elem){l l' : Col}(p : l ~ l')
    → -------------------------
    x ∈ l ↔ x ∈ l'
  ∈-~ x {l}{l'} p =
    proof x ∈ l
      〉 _↔_ 〉 x ∈ to-list l
        :by: to-list-valid
      〉 _↔_ 〉 x ∈ to-list l'
        :by: Perm.∈-~ x p
      〉 _↔_ 〉 x ∈ l'
        :by: isym to-list-valid
    qed
    
open WithListable public

{-# OPTIONS --exact-split --prop --safe #-}
module Collection.Listable.Property where

open import Collection.Definition
open import Collection.Listable.Definition
open import Collection.Listable.Function

open import Universes
import Proposition.Permutation as Perm
import Proposition.Permutation.Class as PermClass
open import Relation.Binary
  hiding (_~_; Reflexive~; Transitive~; Symmetric~)
open import Data.List.Definition
open import Data.List.Collection
open import Data.List.Monoid
open import Data.List.Property
open import Data.List.Operation.Basic
open import Structure.Monoid
open import Logic
open import Proof

∈fold-map : {Col : 𝒰 ˙}{Elem : 𝒱 ˙}
  ⦃ list : Listable 𝒲 Col Elem ⦄
  (f : Elem → List X)
  (l : Col)
  {x : X}
  → -----------------------------
  x ∈ fold-map f l ↔ ∃ λ (e : Elem) → e ∈ l ∧ x ∈ f e
⟶ (∈fold-map f l {x}) p
  with ⟶ (∈mconcat (map f (to-list l)) x) p
⟶ (∈fold-map f l {x}) p | l' , (x∈l' , l'∈map-f)
  with ∈map⁻¹ (to-list l) f x∈l'
⟶ (∈fold-map f l {x}) p
  | .(f e) , (fe∈mapfl , x∈fe) | e , (Id-refl _ , e∈to-list-l) =
  e , (⟵ to-list-valid e∈to-list-l , x∈fe)
⟵ (∈fold-map f l {x}) (e , (e∈l , x∈fe)) =
  ⟵ (∈mconcat (map f (to-list l)) x)
    (f e , (∈map f $ ⟶ to-list-valid e∈l , x∈fe))

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
  open import Data.List.Collection

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

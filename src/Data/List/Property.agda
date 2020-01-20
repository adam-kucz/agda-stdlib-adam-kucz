{-# OPTIONS --safe --exact-split --prop  #-}
open import PropUniverses

module Data.List.Property {𝒰 : Universe} where

open import Data.List.Definition
open import Data.List.Collection

open import Data.Nat
open import Data.Collection
open import Logic
open import Proposition.Identity
open import Proposition.Decidable

instance
  ListListable : {X : 𝒰 ˙} → Listable (List X) X
  to-list ⦃ ListListable ⦄ l = l
  ⟶ (to-list-valid ⦃ ListListable ⦄) p = p
  ⟵ (to-list-valid ⦃ ListListable ⦄) p = p

  ListRemovable : {X : 𝒰 ˙}
    ⦃ d : ∀ {x y : X} → Decidable (x == y) ⦄
    → -----------------------------------
    Removable (List X) X
  remove ⦃ ListRemovable ⦄ _ [] = []
  remove ⦃ ListRemovable ⦄ x (h ∷ _) with decide (h == x)
  remove ⦃ ListRemovable ⦄ x (_ ∷ t) | true _ = remove x t
  remove ⦃ ListRemovable ⦄ x (h ∷ t) | false _ = h ∷ remove x t
  ⟶ (remove-valid ⦃ ListRemovable ⦃ d ⦄ ⦄ {y = y}{h ∷ t}) p
    with decide (h == y) ⦃ d ⦄
  ⟶ (remove-valid ListRemovable {x}{y}{h ∷ t}) p | true _ =
    x∈tail h (∧left ih) , ∧right ih 
    where ih : x ∈ t ∧ x ≠ y
          ih = ⟶ remove-valid p
  ⟶ (remove-valid ListRemovable {S = h ∷ t}) (x∈x∷ l) | false h≠y =
    x∈x∷ t , h≠y
  ⟶ (remove-valid ListRemovable {x}{y} {h ∷ t}) (x∈tail h p) | false h≠y =
    x∈tail h (∧left ih) , ∧right ih
    where ih : x ∈ t ∧ x ≠ y
          ih = ⟶ remove-valid p
  ⟵ (remove-valid ⦃ ListRemovable ⦃ d ⦄ ⦄ {y = y}{h ∷ t}) (x∈h∷t , x≠y)
    with decide (h == y) ⦃ d ⦄
  ⟵ (remove-valid ListRemovable {y = y} {h ∷ t})
    ((x∈x∷ t) , x≠y) | true h==y = ⊥-recursion (h ∈ remove y t) (x≠y h==y)
  ⟵ (remove-valid ListRemovable) (x∈tail _ x∈t , x≠y) | true _ =
    ⟵ remove-valid (x∈t , x≠y)
  ⟵ (remove-valid ListRemovable {y = y} {h ∷ t})
    (x∈x∷ t , x≠y) | false h≠y = x∈x∷ remove y t
  ⟵ (remove-valid ListRemovable {y = y} {h ∷ t})
    (x∈tail h x∈t , x≠y) | false h≠y = x∈tail h (⟵ remove-valid (x∈t , x≠y))

remove-at : (n : ℕ) (l : List X) (p : n < len l) → List X
remove-at zero    (h ∷ l) p = l
remove-at (suc n) (h ∷ l) p = remove-at n l (s<s→-<- p)

open import Data.Functor
open import Function

instance
  ListFunctor : Functor {U = universe-of}(λ X → List X)
  fmap ⦃ ListFunctor ⦄ _ [] = []
  fmap ⦃ ListFunctor ⦄ f (h ∷ t) = f h ∷ fmap f t
  fmap-id ⦃ ListFunctor ⦄ [] = refl []
  fmap-id ⦃ ListFunctor ⦄ (h ∷ t) = List== (refl h) (fmap-id t)
  fmap-∘ ⦃ ListFunctor ⦄ _ _ [] = refl []
  fmap-∘ ⦃ ListFunctor ⦄ g f (h ∷ t) =
    List== (refl (g (f h))) (fmap-∘ g f t)

∈fmap :
  {X : 𝒰 ˙}{Y : 𝒱 ˙}
  {x : X}{l : List X}
  (f : (x : X) → Y)
  (p : x ∈ l)
  → ------------------
  f x ∈ (f <$> l)
∈fmap f (x∈x∷ t) = x∈x∷ f <$> t
∈fmap f (x∈tail h p) = x∈tail (f h) (∈fmap f p)

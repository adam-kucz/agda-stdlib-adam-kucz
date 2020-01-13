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

pattern [_] a₀ = a₀ ∷ []
pattern [_⸴_] a₀ a₁ = a₀ ∷ a₁ ∷ []
pattern [_⸴_⸴_] a₀ a₁ a₂ = a₀ ∷ a₁ ∷ a₂ ∷ []
pattern [_⸴_⸴_⸴_] a₀ a₁ a₂ a₃ = a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ []

remove-at : (n : ℕ) (l : List X) (p : n < len l) → List X
remove-at zero    (h ∷ l) p = l
remove-at (suc n) (h ∷ l) p = remove-at n l (s<s→-<- p)

open import Data.Functor

instance
  ListFunctor : Functor {𝒰 = 𝒰} List
  fmap ⦃ ListFunctor ⦄ _ [] = []
  fmap ⦃ ListFunctor ⦄ f (h ∷ t) = f h ∷ fmap f t
  fmap-id ⦃ ListFunctor ⦄ [] = refl []
  fmap-id ⦃ ListFunctor ⦄ (h ∷ t) = List== (refl h) (fmap-id t)
  fmap-∘ ⦃ ListFunctor ⦄ _ _ [] = refl []
  fmap-∘ ⦃ ListFunctor ⦄ g f (h ∷ t) =
    List== (refl (g (f h))) (fmap-∘ g f t)

open import Data.Maybe

module WithDecidableElement==
  {X : 𝒰 ˙}
  ⦃ d : {x y : X} → Decidable (x == y) ⦄
  where
  
  find : (x : X) (l : List X) → Maybe ℕ
  find x [] = nothing
  find x (h ∷ l) with decide (x == h)
  find x (h ∷ l) | true  _ = just 0
  find x (h ∷ l) | false _ = fmap suc (find x l)
  
  index : {x : X} {l : List X} (p : x ∈ l) → ℕ
  index {x = x} {h ∷ l} p with decide (x == h)
  index {x = x} {h ∷ l} p | true   x==h = 0
  index {x = x} {h ∷ l} p | false ¬x==h = suc (index (prev p))
    where open import Proposition.Empty
          prev : (p : x ∈ h ∷ l) → x ∈ l
          prev (x∈x∷ t) = ⊥-recursionₚ (x ∈ l) (¬x==h (refl x))
          prev (x∈tail _ p) = p
  
  multiplicity : (x : X) (l : List X) → ℕ
  multiplicity x [] = 0
  multiplicity x (h ∷ l) with decide (x == h)
  multiplicity x (h ∷ l) | true  _ = suc (multiplicity x l)
  multiplicity x (h ∷ l) | false _ = multiplicity x l

open WithDecidableElement== public

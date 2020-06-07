{-# OPTIONS --exact-split --prop --safe #-}
module Data.List.Property where

open import Data.List.Definition
open import Data.List.Collection
open import Data.List.Operation.Basic

open import PropUniverses
open import Proposition.Identity hiding (refl)
open import Proposition.Decidable
open import Collection.Definition
open import Collection.Basic
open import Collection.Removable
open import Collection.Operation.Definition
open import Collection.Listable.Definition
open import Structure.Monoid.Definition
open import Logic

instance
  ListEmpty : Empty (List X) X
  ListListable : Listable 𝒰₀ (List X) X
  ListUnion : Union (List X) X
  ListRemovable :
    ⦃ d : HasDecidableIdentity X ⦄
    → -----------------------------------
    Removable (List X) X
  ListIntersection :
    ⦃ d : HasDecidableIdentity X ⦄
    → -----------------------------------
    Intersection (List X) X
  ListDecidable∈ :
    ⦃ d : HasDecidableIdentity X ⦄
    → ----------------------------------------
    ∀ {x : X}{l : List X} → Decidable (x ∈ l)
  ListDecidable== :
    ⦃ d : HasDecidableIdentity X ⦄
    → ----------------------------------------
    HasDecidableIdentity (List X)

∅ ⦃ ListEmpty ⦄ = []
_∉∅ ⦃ ListEmpty ⦄ _ ()

collection ⦃ ListListable ⦄ = ListCollection
to-list ⦃ ListListable ⦄ S = S
⟶ (to-list-valid ⦃ ListListable ⦄) p = p
⟵ (to-list-valid ⦃ ListListable ⦄) q = q

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

open import Proof

_∪_ ⦃ ListUnion ⦄ = _++_
⟶ (∪-valid ⦃ ListUnion ⦄ {x} {[]} {S₁}) p = ∨right p
⟶ (∪-valid ⦃ ListUnion ⦄ {x} {x ∷ S₀} {S₁}) (x∈x∷ .(S₀ ∪ S₁)) =
  ∨left (x∈x∷ S₀) 
⟶ (∪-valid ⦃ ListUnion ⦄ {x} {h ∷ S₀} {S₁}) (x∈tail h p)
  with ⟶ (∪-valid {S₀ = S₀}) p
⟶ (∪-valid ListUnion {x} {h ∷ S₀} {S₁}) (x∈tail h p) | ∨left p₁ =
  ∨left (x∈tail h p₁)
⟶ (∪-valid ListUnion {x} {h ∷ S₀} {S₁}) (x∈tail h p) | ∨right q =
  ∨right q
⟵ (∪-valid ⦃ ListUnion ⦄ {x} {[]} {S₁}) (∨right q) = q
⟵ (∪-valid ⦃ ListUnion ⦄ {x} {x ∷ S₀} {S₁}) (∨left (x∈x∷ S₀)) =
  x∈x∷ (S₀ ∪ S₁)
⟵ (∪-valid ⦃ ListUnion ⦄ {x} {h ∷ S₀} {S₁}) (∨left (x∈tail h p)) =
  x∈tail h $ ⟵ (∪-valid {S₀ = S₀}) $ ∨left p
⟵ (∪-valid ⦃ ListUnion ⦄ {x} {h ∷ S₀} {S₁}) (∨right q) =
  x∈tail h $ ⟵ (∪-valid {S₀ = S₀}) $ ∨right q

open import Logic.Proof

_∩_ ⦃ ListIntersection ⦄ S₀ S₁ = remove-all (remove-all S₀ S₁) S₁
∩-valid ⦃ ListIntersection ⦄ {x}{S₀}{S₁} =
  proof x ∈ S₀ ∩ S₁
    〉 _↔_ 〉 x ∈ S₁ ∧ x ∉ remove-all S₀ S₁
      :by: remove-all-prop {l = remove-all S₀ S₁}
    〉 _↔_ 〉 x ∈ S₁ ∧ ¬ (x ∈ S₁ ∧ x ∉ S₀)
      :by: step1
    〉 _↔_ 〉 x ∈ S₀ ∧ x ∈ S₁
      :by: step2
  qed
  where step1 : x ∈ S₁ ∧ x ∉ remove-all S₀ S₁
                ↔
                x ∈ S₁ ∧ ¬ (x ∈ S₁ ∧ x ∉ S₀)
        ⟶ step1 (left , right) =
          left , λ r → right $ ⟵ remove-all-prop r
        ⟵ step1 (left , right) = left , λ r → right $ ⟶ remove-all-prop r
        step2 : x ∈ S₁ ∧ ¬ (x ∈ S₁ ∧ x ∉ S₀) ↔ x ∈ S₀ ∧ x ∈ S₁
        ⟶ step2 (left , right) with decide (x ∈ S₀)
        ⟶ step2 (left , right) | true p = p , left
        ⟶ step2 (left , right) | false ¬p =
          ⊥-recursion _ $ right (left , ¬p)
        ⟵ step2 (left , right) = right , λ {(_ , p) → p left}

open import Relation.Binary

ListDecidable∈ {l = []} = false (λ ())
ListDecidable∈ {x = x}{h ∷ l} with decide (x == h)
ListDecidable∈ {x = x} {h ∷ l} | true p =
  true (Id.coe (ap (λ — → x ∈ — ∷ l) p) (x∈x∷ l))
ListDecidable∈ {x = x} {h ∷ l} | false ¬p with decide (x ∈ l)
ListDecidable∈ {x = x} {h ∷ l} | false ¬p | true p = true (x∈tail h p)
ListDecidable∈ {x = x} {h ∷ l} | false ¬p | false ¬p₁ =
  false (λ { (x∈x∷ t) → ¬p (Id.refl x) ; (x∈tail h q) → ¬p₁ q })

ListDecidable== {x = []} {[]} = true (Id.refl [])
ListDecidable== {x = []} {h ∷ y} = false λ ()
ListDecidable== {x = h ∷ x} {[]} = false λ ()
ListDecidable== {x = h₀ ∷ x} {h₁ ∷ y} with ListDecidable== {x = x}{y}
ListDecidable== ⦃ d = _ ⦄ {h₀ ∷ x} {h₁ ∷ y} | true q =
  dif h₀ == h₁
    then (λ p → true (ap2 _∷_ p q))
    else (λ ¬p → false λ { (Id.refl _) → ¬p $ Id.refl h₀})
ListDecidable== ⦃ d = _ ⦄ {h₀ ∷ x} {h₁ ∷ y} | false ¬q =
  false λ { (Id.refl _) → ¬q $ Id.refl x}

-∈[-]↔== : {x y : X} →
  x ∈ [ y ] ↔ x == y
⟶ -∈[-]↔== (x∈x∷ []) = Id.refl _
⟵ -∈[-]↔== (Id.refl x) = x∈x∷ []



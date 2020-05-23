{-# OPTIONS --exact-split --prop --safe #-}
module Data.List.Property where

open import Data.List.Definition
open import Data.List.Collection
open import Data.List.Operation.Basic

open import PropUniverses
open import Proposition.Identity hiding (refl)
open import Proposition.Decidable.Definition
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
    ⦃ d : ∀ {x y : X} → Decidable (x == y) ⦄
    → -----------------------------------
    Removable (List X) X
  ListIntersection :
    ⦃ d : ∀ {x y : X} → Decidable (x == y) ⦄
    → -----------------------------------
    Intersection (List X) X
  ListDecidable∈ : {X : 𝒰 ˙}
    ⦃ d : ∀ {x y : X} → Decidable (x == y) ⦄
    → ----------------------------------------
    ∀ {x : X}{l : List X} → Decidable (x ∈ l)

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
  false (λ { (x∈x∷ t) → ¬p (Id-refl x) ; (x∈tail h q) → ¬p₁ q })

-∈[-]↔== : {x y : X} →
  x ∈ [ y ] ↔ x == y
⟶ -∈[-]↔== (x∈x∷ []) = Id-refl _
⟵ -∈[-]↔== (Id-refl x) = x∈x∷ []

-- remove-at : (n : ℕ) (l : List X) (p : n < len l) → List X
-- remove-at zero    (h ∷ l) p = l
-- remove-at (suc n) (h ∷ l) p = remove-at n l (s<s→-<- p)

-- private
--   remove-duplicates' :
--     ⦃ d : ∀ {x y : X} → Decidable (x == y) ⦄
--     (l : List X)
--     (n : ℕ)
--     (p : len l < n)
--     → -----------------------------------------
--     List X

-- remove-duplicates' [] n p = []
-- remove-duplicates' (_ ∷ _) zero ()
-- remove-duplicates' {X = X} ⦃ d ⦄ (h ∷ t) (n +1) p =
--   h ∷ remove-duplicates' (remove h t) n (
--     proof len (remove h t)
--       〉 _≤_ 〉 len t         :by: len-remove-≤ h t
--       〉 _<_ 〉 n             :by: s<s→-<- p
--     qed)
--   where len-remove-≤ : (x : X)(l : List X) → len (remove x l) ≤ len l
--         len-remove-≤ x [] = refl 0
--         len-remove-≤ x (h ∷ l) with decide (h == x) ⦃ d ⦄
--         len-remove-≤ x (h ∷ l) | true _ = ∨right (
--           proof len (remove x l)
--             〉 _≤_ 〉 len l         :by: len-remove-≤ x l
--             〉 _<_ 〉 len l +1      :by: postfix suc (len l)
--           qed)
--         len-remove-≤ x (h ∷ l) | false _ = ap suc $ len-remove-≤ x l

-- remove-duplicates :
--   ⦃ d : ∀ {x y : X} → Decidable (x == y) ⦄
--   → -----------------------------------
--   (l : List X) → List X
-- remove-duplicates {X = X} ⦃ d ⦄ l =
--   remove-duplicates' l (len l +1) (postfix suc (len l))

-- private
--   ∈remove-duplicates' :
--     ⦃ d : ∀ {x y : X} → Decidable (x == y) ⦄
--     {l : List X}
--     {n : ℕ}
--     {p : len l < n}
--     {x : X}
--     → ------------------------------------------
--     x ∈ remove-duplicates' l n p ↔ x ∈ l

-- ⟶ (∈remove-duplicates' {l = h ∷ l} {n +1}) (x∈x∷ _) = x∈x∷ l
-- ⟶ (∈remove-duplicates' {l = h ∷ l} {n +1}) (x∈tail .h p) =
--   x∈tail h $
--   ∧left $
--   ⟶ remove-valid $
--   ⟶ ∈remove-duplicates' p
-- ⟵ (∈remove-duplicates' {l = h ∷ t}{n +1}{x = x}) q with decide (x == h)
-- ⟵ (∈remove-duplicates' {l = h ∷ t} {n +1} {x = .h}) q
--   | true (Id.refl .h) = x∈x∷ _
-- ⟵ (∈remove-duplicates' {l = h ∷ t}{n +1}{x = x}) (x∈x∷ .t)
--   | false ¬p = x∈x∷ _
-- ⟵ (∈remove-duplicates' {l = h ∷ t}{n +1}{x = x}) (x∈tail h q)
--   | false ¬p =
--   x∈tail h $
--   ⟵ (∈remove-duplicates' {l = remove h t}) $
--   ⟵ remove-valid (q , ¬p)

-- ∈remove-duplicates :
--   ⦃ d : ∀ {x y : X} → Decidable (x == y) ⦄
--   {l : List X}
--   {x : X}
--   → ------------------------------------------
--   x ∈ remove-duplicates l ↔ x ∈ l
-- ∈remove-duplicates = ∈remove-duplicates'

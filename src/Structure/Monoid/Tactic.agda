{-# OPTIONS --exact-split --safe --prop #-}
module Structure.Monoid.Tactic where

open import Structure.Monoid.Definition

open import Universes
open import Proposition.Identity hiding (refl)
open import Data.Nat
open import Collection

data BinaryTree (X : 𝒰 ˙) : 𝒰 ˙ where
  leaf : (x : X) → BinaryTree X
  node : (l r : BinaryTree X) → BinaryTree X
  
instance
  TreeCollection : {X : 𝒰 ˙} → Collection 𝒰 (BinaryTree X) X
  TreeListable : {X : 𝒰 ˙} → Listable 𝒰 (BinaryTree X) X

open import Relation.Binary

module BT where
  data member {X : 𝒰 ˙} : Rel 𝒰 X (BinaryTree X) where
    ∈leaf : ∀ x → member x (leaf x)
    ∈left : ∀ {y l}(p : member y l) r → member y (node l r)
    ∈right : ∀ {y} l {r}(p : member y r) → member y (node l r)

_∈_ ⦃ TreeCollection ⦄ = BT.member

open import Data.List as L
open import Logic
open import Proof

collection ⦃ TreeListable ⦄ = TreeCollection
to-list ⦃ TreeListable ⦄ (leaf x) = [ x ]
to-list ⦃ TreeListable ⦄ (node l r) = to-list l ∪ to-list r
⟶ (to-list-valid ⦃ TreeListable ⦄) (BT.∈leaf x) = x∈x∷ []
⟶ (to-list-valid ⦃ TreeListable ⦄) (BT.∈left p r) =
  ⟵ (∪-valid {S₁ = to-list r}) $ ∨left $ ⟶ to-list-valid p
⟶ (to-list-valid ⦃ TreeListable ⦄) (BT.∈right l p) =
  ⟵ (∪-valid {S₀ = to-list l}) $ ∨right $ ⟶ to-list-valid p
⟵ (to-list-valid ⦃ TreeListable ⦄ {leaf x}) (x∈x∷ []) = BT.∈leaf x
⟵ (to-list-valid ⦃ TreeListable ⦄ {node l r}) q
  with ⟶ (∪-valid {S₀ = to-list l}{S₁ = to-list r}) q
⟵ (to-list-valid TreeListable {node l r}) q | ∨left p =
  BT.∈left (⟵ to-list-valid p) r
⟵ (to-list-valid TreeListable {node l r}) q | ∨right p =
  BT.∈right l $ ⟵ to-list-valid p

open import Data.Nat.Proof
open import Function.Proof

tree-to-list-len : (t : BinaryTree X) → 1 ≤ len (to-list t)
tree-to-list-len (leaf x) = refl 1
tree-to-list-len (node l r) with to-list l
tree-to-list-len (node l r) | [] = tree-to-list-len r
tree-to-list-len (node l r) | h ∷ t = postfix (_+ len (t ∪ to-list r)) 1

open import Data.Vec
open import Proposition.Decidable

-- module Sort
--     (_≤_ : BinRel 𝒰 X)
--     ⦃ dec≤ : ∀ {x y} → Decidable (x ≤ y) ⦄
--     ⦃ dec== : HasDecidableIdentity X ⦄
--     where

--   find-min : (v : Vec X m)(min : X) → X
--   find-min [] min = min
--   find-min (h ∷ v) min = find-min v (if h ≤ min then h else min)

--   find-min∈ : ∀ (v : Vec X m) min → find-min v min ∈ min ∷ v
--   find-min∈ [] x = x∈x∷ []
--   find-min∈ (h ∷ v) x with decide (h ≤ x) ⦃ dec≤ ⦄
--   find-min∈ (h ∷ v) x | true _ = x∈tail x (find-min∈ v h)
--   find-min∈ (h ∷ v) x | false _ =
--     ∈insert-2 (find-min v x) x h v $ find-min∈ v x
--     where ∈insert-2 :
--             (x h₀ h₁ : X)
--             (t : Vec X m)
--             (p : x ∈ h₀ ∷ t)
--             → ----------------
--             x ∈ h₀ ∷ h₁ ∷ t
--           ∈insert-2 x x h₁ t (x∈x∷ t₁) = x∈x∷ (h₁ ∷ t)
--           ∈insert-2 x h₀ h₁ t (x∈tail h₀ p) = x∈tail h₀ (x∈tail h₁ p)

--   vec-sort : (l : Vec X m) → Vec X m
--   vec-sort [] = []
--   vec-sort (h ∷ t) = elem ∷ vec-sort (vec-remove elem (h ∷ t) (find-min∈ t h))
--     where elem = find-min t h

--   sort : (l : List X) → List X
--   sort l = to-list (vec-sort (to-vec l))
  
--   sort-valid : ∀ (x : X) l → x ∈ sort l ↔ x ∈ l
--   ⟶ (sort-valid x l) p = {!!}
--   ⟵ (sort-valid x (x ∷ t)) (x∈x∷ t) = {!!}
--   ⟵ (sort-valid x (h ∷ _)) (x∈tail h q) = {!!}
  
--   len-sort : ∀ l → len (sort l) == len l
--   len-sort l = vec-to-list-len (vec-sort (to-vec l))

open import Function hiding (_$_)

module WithMonoid ⦃ mon : Monoid X ⦄ where
  Interpret : (X : 𝒰 ˙)(t : BinaryTree ℕ) → 𝒰 ˙
  Interpret X t = ∀ (x : ℕ)(p : x ∈ t) → X
  
  eval-tree : (t : BinaryTree ℕ)(values : Interpret X t) → X
  eval-tree (leaf x) values = values x (BT.∈leaf x)
  eval-tree (node l r) values = eval-tree l val-l ∙ eval-tree r val-r
    where val-l : Interpret X l
          val-l x p = values x (BT.∈left p r)
          val-r : Interpret X r
          val-r x p = values x (BT.∈right l p)

  open import Operation.Binary

  comm-monoid : 

  comm-monoid-tactic :
    ⦃ mon : Monoid X ⦄
    ⦃ com : Commutative (_∙_ ⦃ mon ⦄) ⦄
    (t₀ t₁ : BinaryTree ℕ)
    (p : to-list t₀ ~ to-list t₁)
    (values : Interpret X t₀)
    → -------------------------------------------
    let values' : Interpret X t₁
        values' x q = values x (
          ⟵ to-list-valid $
          ⟶ (sort-valid x (to-list t₀)) $
          Id.coe (ap (x ∈_) $ sym p) $
          ⟵ (sort-valid x (to-list t₁)) $
          ⟶ to-list-valid q)
    in eval-tree t₀ values == eval-tree t₁ values'
  comm-monoid-tactic (leaf x) (leaf .x) (Id.refl _) values =
    refl (values x _)
  comm-monoid-tactic (leaf x) (node t₁ t₂) p values
    with antisym (∨right (s<s (z<s {0}))) (
      proof 2
        〉 _≤_ 〉 len (to-list t₁) + len (to-list t₂)
          :by: ap2 _+_ (tree-to-list-len t₁) (tree-to-list-len t₂)
        〉 _==_ 〉 len (to-list t₁ ∪ to-list t₂)
          :by: sym $ len++ (to-list t₁) (to-list t₂)
        〉 _==_ 〉 len (sort (to-list t₁ ∪ to-list t₂))
          :by: sym $ len-sort (to-list t₁ ∪ to-list t₂) 
        〉 _==_ 〉 len (sort [ x ])
          :by: ap len $ sym p
        〉 _==_ 〉 1
          :by: len-sort [ x ]
      qed)
  comm-monoid-tactic (leaf x) (node t₁ t₂) p values | ()
  comm-monoid-tactic (node t₁ t₂) (leaf x) p values
      with antisym (∨right (s<s (z<s {0}))) (
      proof 2
        〉 _≤_ 〉 len (to-list t₁) + len (to-list t₂)
          :by: ap2 _+_ (tree-to-list-len t₁) (tree-to-list-len t₂)
        〉 _==_ 〉 len (to-list t₁ ∪ to-list t₂)
          :by: sym $ len++ (to-list t₁) (to-list t₂)
        〉 _==_ 〉 len (sort (to-list t₁ ∪ to-list t₂))
          :by: sym $ len-sort (to-list t₁ ∪ to-list t₂) 
        〉 _==_ 〉 len (sort [ x ])
          :by: ap len p
        〉 _==_ 〉 1
          :by: len-sort [ x ]
      qed)
  comm-monoid-tactic (node t₀ t₁) (leaf x) p values | ()
  comm-monoid-tactic (node t₀ t₁) (node t₂ t₃) p values =
    proof eval-tree t₀ _ ∙ eval-tree t₁ _
      === eval-tree t₂ _ ∙ eval-tree t₃ _
        :by: {!!}
    qed
    where values' : Interpret X (node t₂ t₃)
          values' x q = values x (
            ⟵ to-list-valid $
            ⟶ (sort-valid x (to-list t₀ ∪ to-list t₁)) $
            Id.coe (ap (x ∈_) $ sym p) $
            ⟵ (sort-valid x (to-list t₂ ∪ to-list t₃)) $
            ⟶ to-list-valid q)

{-# OPTIONS --safe --exact-split --prop  #-}
module Data.Tree.Binary.Property where

open import Data.Tree.Binary.Definition

open import PropUniverses

data member {X : 𝒰 ˙} : (x : X)(t : BinaryTree X) → 𝒰 ᵖ where
  _∈leaf : (x : X) → member x (leaf x)
  _∈left_/\_ :
    (x : X)
    {l : BinaryTree X}
    (p : member x l)
    (r : BinaryTree X)
    → -----------------------------------------------
    member x (l /\ r)
  _∈right_/\_ :
    (x : X)
    (l : BinaryTree X)
    {r : BinaryTree X}
    (p : member x r)
    → -----------------------------------------------
    member x (l /\ r)

open import Proposition.Decidable
open import Collection hiding (_++_)

instance
  BinaryTreeCollection : {X : 𝒰 ˙} → Collection 𝒰 (BinaryTree X) X
  BinaryTreeListable : {X : 𝒰 ˙} → Listable 𝒰 (BinaryTree X) X
  BinaryTreeUnion : Union (BinaryTree X) X
  BinaryTreeDecidable∈ :
    ⦃ d : HasDecidableIdentity X ⦄
    → ----------------------------------------
    ∀ {x : X}{t : BinaryTree X} → Decidable (x ∈ t)

_∈_ ⦃ BinaryTreeCollection ⦄ = member

open import Data.List
open import Logic
open import Proof

collection ⦃ BinaryTreeListable ⦄ = BinaryTreeCollection
to-list ⦃ BinaryTreeListable ⦄ (leaf x) = [ x ]
to-list ⦃ BinaryTreeListable ⦄ (l /\ r) = to-list l ++ to-list r
⟶ (to-list-valid ⦃ BinaryTreeListable ⦄) (x ∈leaf) = x∈x∷ []
⟶ (to-list-valid ⦃ BinaryTreeListable ⦄ {l /\ r}) (x ∈left p /\ r) =
  ⟵ (∈++ (to-list l) (to-list r)) $ ∨left $ ⟶ to-list-valid p
⟶ (to-list-valid ⦃ BinaryTreeListable ⦄ {l /\ r}) (x ∈right l /\ p) =
  ⟵ (∈++ (to-list l) (to-list r)) $ ∨right $ ⟶ to-list-valid p
⟵ (to-list-valid ⦃ BinaryTreeListable ⦄ {leaf x}) (x∈x∷ []) = x ∈leaf
⟵ (to-list-valid ⦃ BinaryTreeListable ⦄ {l /\ r}) q
  with ⟶ (∈++ (to-list l) (to-list r)) q
⟵ (to-list-valid BinaryTreeListable {l /\ r}{x}) q | ∨left p =
  x ∈left ⟵ (to-list-valid ⦃ BinaryTreeListable ⦄) p /\ r
⟵ (to-list-valid BinaryTreeListable {l /\ r}{x}) q | ∨right p =
  x ∈right l /\ ⟵ (to-list-valid ⦃ BinaryTreeListable ⦄) p

_∪_ ⦃ BinaryTreeUnion ⦄ = _/\_
⟶ (∪-valid ⦃ BinaryTreeUnion ⦄) (x ∈left p /\ r) = ∨left p
⟶ (∪-valid ⦃ BinaryTreeUnion ⦄) (x ∈right l /\ p) = ∨right p
⟵ (∪-valid ⦃ BinaryTreeUnion ⦄ {x}{l}{r}) (∨left p) = x ∈left p /\ r
⟵ (∪-valid ⦃ BinaryTreeUnion ⦄ {x}{l}{r}) (∨right q) = x ∈right l /\ q

BinaryTreeDecidable∈ {x = x} {leaf y} with decide (x == y)
BinaryTreeDecidable∈ {x = x} {leaf y} | true p =
  true (Id.coe (ap (λ — → x ∈ leaf —) p) $ x ∈leaf)
BinaryTreeDecidable∈ {x = x} {leaf y} | false ¬p =
  false λ { (x ∈leaf) → ¬p $ Id.refl x}
BinaryTreeDecidable∈ {x = x} {l /\ r}
  with BinaryTreeDecidable∈ {x = x}{l}
BinaryTreeDecidable∈ {x = x} {l /\ r} | true p = true (x ∈left p /\ r)
BinaryTreeDecidable∈ {x = x} {l /\ r} | false ¬p
  with BinaryTreeDecidable∈ {x = x}{r}
BinaryTreeDecidable∈ {x = x} {l /\ r} | false ¬p | true p =
  true (x ∈right l /\ p)
BinaryTreeDecidable∈ {x = x} {l /\ r} | false ¬p | false ¬q =
  false (λ { (x ∈left p /\ r) → ¬p p
           ; (x ∈right l /\ q) → ¬q q})

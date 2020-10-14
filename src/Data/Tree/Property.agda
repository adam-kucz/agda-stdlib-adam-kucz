{-# OPTIONS --safe --exact-split  #-}
-- TODO: fix termination
module Data.Tree.Property where

open import Data.Tree.Definition

open import Universes
open import Data.List hiding (member)
open import Logic
open import Collection hiding (_++_)

data member {X : 𝒰 ˙} : (x : X)(t : Tree X) → 𝒰 ˙ where
  _∈leaf : (x : X) → member x (leaf x)
  _∈branch_ :
    (x : X)
    {l : List (Tree X)}
    (p : ∃ λ (br : Tree X) → br ∈ l ∧ member x br)
    → -----------------------------------------------
    member x (branch l)

open import Type.Decidable

instance
  TreeCollection : {X : 𝒰 ˙} → Collection 𝒰 (Tree X) X
  TreeEmpty : Empty (Tree X) X
  TreeListable : {X : 𝒰 ˙} → Listable 𝒰 (Tree X) X
  TreeUnion : Union (Tree X) X
  -- TreeRemovable :
  --   ⦃ d : HasDecidableIdentity X ⦄
  --   → ----------------------------------------
  --   Removable (Tree X) X
  TreeDecidable∈ :
    ⦃ d : HasDecidableIdentity X ⦄
    → ----------------------------------------
    ∀ {x : X}{t : Tree X} → Decidable (x ∈ t)


open import Structure.Monoid
open import Proof

_∈_ ⦃ TreeCollection ⦄ = member

∅ ⦃ TreeEmpty ⦄ = ◻
_∉∅ ⦃ TreeEmpty ⦄ x (x ∈branch (_ , ()))

collection ⦃ TreeListable ⦄ = TreeCollection
to-list ⦃ TreeListable ⦄ (leaf x) = [ x ]
to-list ⦃ TreeListable ⦄ ◻ = []
to-list ⦃ TreeListable ⦄ (branch (h ∷ t)) =
  to-list ⦃ TreeListable ⦄ h ++ to-list ⦃ TreeListable ⦄ (branch t)
⟶ (to-list-valid ⦃ TreeListable ⦄ {leaf x}) (x ∈leaf) = x∈x∷ []
⟶ (to-list-valid ⦃ TreeListable ⦄ {◻}) (_ ∈branch (_ , ()))
⟶ (to-list-valid ⦃ TreeListable ⦄ {branch (h ∷ br)})
  (x ∈branch (h , (x∈x∷ br , x∈h))) =
  ⟵ (∈++ (to-list h) (to-list (branch br))) $
  ∨left $ ⟶ to-list-valid x∈h
⟶ (to-list-valid ⦃ TreeListable ⦄ {branch (h ∷ br)})
  (x ∈branch (t , (x∈tail h t∈br , x∈t))) =
  ⟵ (∈++ (to-list h) (to-list (branch br))) $
  ∨right $ ⟶ to-list-valid $ x ∈branch (t , (t∈br , x∈t))
⟵ (to-list-valid ⦃ TreeListable ⦄ {leaf x}) (x∈x∷ []) = x ∈leaf
⟵ (to-list-valid ⦃ TreeListable ⦄ {branch (h ∷ br)}) q
  with ⟶ (∈++ (to-list h) (to-list (branch br))) q
⟵ (to-list-valid TreeListable {branch (h ∷ br)}) q | ∨left p =
  _ ∈branch (h , (x∈x∷ br , ⟵ to-list-valid p))
⟵ (to-list-valid TreeListable {branch (h ∷ br)}) q | ∨right p
  with ⟵ (to-list-valid ⦃ TreeListable ⦄ {branch br}) p
⟵ (to-list-valid TreeListable {branch (h ∷ br)}) q
  | ∨right p | x ∈branch (t , (t∈br , x∈t)) =
  x ∈branch (t , (x∈tail h t∈br , x∈t))

_∪_ ⦃ TreeUnion ⦄ = _/\_
⟶ (∪-valid ⦃ TreeUnion ⦄) (x ∈branch (l , (x∈x∷ _ , x∈l))) =
  ∨left x∈l
⟶ (∪-valid ⦃ TreeUnion ⦄) (x ∈branch (r , (x∈tail h (x∈x∷ []) , x∈r))) =
  ∨right x∈r
⟵ (∪-valid ⦃ TreeUnion ⦄ {x}{l}{r}) (∨left p) =
  x ∈branch (l , (x∈x∷ [ r ] , p))
⟵ (∪-valid ⦃ TreeUnion ⦄ {x}{l}{r}) (∨right q) =
  x ∈branch (r , (x∈tail l (x∈x∷ []) , q))

open import Function hiding (_$_)

{-
remove ⦃ TreeRemovable {X = X} ⦄ x' = trim ∘ go
  where go : Tree X → Tree X
        go (leaf x) = if x' == x then ◻ else leaf x
        go ◻ = ◻
        go (branch (h ∷ br)) =
          branch (cons (go h) (go (branch br)))
⟶ (remove-valid ⦃ TreeRemovable ⦄ {S = S}) p = {!!}
⟵ (remove-valid ⦃ TreeRemovable ⦃ d ⦄ ⦄ {y = y})
  ((x ∈leaf) , x≠y) with decide (y == x) ⦃ d ⦄
⟵ (remove-valid (TreeRemovable ⦃ d = d ⦄) {y = y})
  ((x ∈leaf) , x≠y) | true p = ⊥-recursion _ $ x≠y $ sym p
⟵ (remove-valid (TreeRemovable ⦃ d = d ⦄) {y = y})
  ((x ∈leaf) , x≠y) | false ¬p = x ∈leaf
⟵ (remove-valid ⦃ TreeRemovable ⦄) (_∈branch_ x {h ∷ l} (t , (t∈br , x∈t)) , x≠y) = {!!}
-}

∈tail :
  ∀{x : X}{br}
  h
  (p : x ∈ branch br)
  → ----------------------------------------
  x ∈ branch (h ∷ br)
∈tail h (x ∈branch (t , (t∈br , x∈t))) =
  x ∈branch (t , (x∈tail h t∈br , x∈t))

TreeDecidable∈ {x = x} {leaf y} with decide (x == y)
TreeDecidable∈ {x = x} {leaf x} | true (Id.refl x) = true $ x ∈leaf
TreeDecidable∈ {x = x} {leaf y} | false ¬p = false λ { (x ∈leaf) → ¬p $ Id.refl x}
TreeDecidable∈ {x = x} {◻} = false (x ∉∅)
TreeDecidable∈ {x = x} {branch (h ∷ br)} with TreeDecidable∈ {x = x} {h}
TreeDecidable∈ {x = x} {branch (h ∷ br)} | true p =
  true (x ∈branch (h , (x∈x∷ br , p)))
TreeDecidable∈ {x = x} {branch (h ∷ br)} | false ¬p
  with TreeDecidable∈ {x = x}{branch br}
TreeDecidable∈ {x = x} {branch (h ∷ br)} | false ¬p | true p = true (∈tail h p)
TreeDecidable∈ {x = x} {branch (h ∷ br)} | false ¬p | false ¬q = false λ
  { (x ∈branch (h , ((x∈x∷ t) , x∈h))) → ¬p x∈h
  ; (x ∈branch (t , (x∈tail h t∈br , x∈t))) →
    ¬q (x ∈branch (t , (t∈br , x∈t)))}

{-# OPTIONS --exact-split --safe --prop #-}
module Structure.Semigroup.Tactic where

open import Structure.Semigroup.Definition

open import Universes
open import Proposition.Identity hiding (refl)
open import Data.Nat hiding (_⊔_)
open import Collection

data BinaryTree (X : 𝒰 ˙) : 𝒰 ˙ where
  leaf : (x : X) → BinaryTree X
  node : (l r : BinaryTree X) → BinaryTree X
  
instance
  TreeCollection : {X : 𝒰 ˙} → Collection 𝒰 (BinaryTree X) X
  TreeListable : {X : 𝒰 ˙} → Listable 𝒰 (BinaryTree X) X

open import Relation.Binary hiding (_~_)

module BT where
  data member {X : 𝒰 ˙} : Rel 𝒰 X (BinaryTree X) where
    ∈leaf : ∀ x → member x (leaf x)
    ∈left : ∀ {y l}(p : member y l) r → member y (node l r)
    ∈right : ∀ {y} l {r}(p : member y r) → member y (node l r)

_∈_ ⦃ TreeCollection ⦄ = BT.member

open import Data.List as L hiding ([_])
open import Logic hiding (⊥-recursion)
open import Proof

collection ⦃ TreeListable ⦄ = TreeCollection
to-list ⦃ TreeListable ⦄ (leaf x) = L.[ x ]
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

open import Data.NonemptyList

to-nonempty-list : (t : BinaryTree X) → NonemptyList X
to-nonempty-list (leaf x) = [ x ]
to-nonempty-list (node l r) = to-nonempty-list l ∪ to-nonempty-list r

to-nonempty-list-valid : ∀ {x : X}{t}
  → -------------------------------------
  x ∈ t ↔ x ∈ to-nonempty-list t
⟶ to-nonempty-list-valid (BT.∈leaf x) = ∈[ x ]
⟶ to-nonempty-list-valid (BT.∈left p r) =
  ⟵ ∪-valid $ ∨left $ ⟶ to-nonempty-list-valid p
⟶ to-nonempty-list-valid (BT.∈right l p) = 
  ⟵ (∪-valid {S₀ = to-nonempty-list l}) $
  ∨right $
  ⟶ to-nonempty-list-valid p
⟵ (to-nonempty-list-valid {t = leaf x}) ∈[ x ] = BT.∈leaf x
⟵ (to-nonempty-list-valid {t = node l r}) q
  with ⟶ (∪-valid {S₀ = to-nonempty-list l}) q
⟵ (to-nonempty-list-valid {x = _} {node l r}) q | ∨left p =
  BT.∈left (⟵ to-nonempty-list-valid p) r
⟵ (to-nonempty-list-valid {x = _} {node l r}) q | ∨right p =
  BT.∈right l $ ⟵ to-nonempty-list-valid p

-- open import Data.Nat.Proof
-- open import Function.Proof

-- tree-to-list-len : (t : BinaryTree X) → 1 ≤ len (to-list t)
-- tree-to-list-len (leaf x) = refl 1
-- tree-to-list-len (node l r) with to-list l
-- tree-to-list-len (node l r) | [] = tree-to-list-len r
-- tree-to-list-len (node l r) | h ∷ t = postfix (_+ len (t ∪ to-list r)) 1

open import Data.Vec as V hiding ([_])
open import Proposition.Decidable

module Sort
    (_≤_ : BinRel 𝒰 X)
    ⦃ dec≤ : ∀ {x y} → Decidable (x ≤ y) ⦄
    ⦃ dec== : HasDecidableIdentity X ⦄
    where

  find-min : (v : Vec X m)(min : X) → X
  find-min [] min = min
  find-min (h ∷ v) min = find-min v (if h ≤ min then h else min)

  find-min∈ : ∀ (v : Vec X m) min → find-min v min ∈ min ∷ v
  find-min∈ [] x = x∈x∷ []
  find-min∈ (h ∷ v) x with decide (h ≤ x) ⦃ dec≤ ⦄
  find-min∈ (h ∷ v) x | true _ = x∈tail x (find-min∈ v h)
  find-min∈ (h ∷ v) x | false _ =
    ∈insert-2 (find-min v x) x h v $ find-min∈ v x
    where ∈insert-2 :
            (x h₀ h₁ : X)
            (t : Vec X m)
            (p : x ∈ h₀ ∷ t)
            → ----------------
            x ∈ h₀ ∷ h₁ ∷ t
          ∈insert-2 x x h₁ t (x∈x∷ t₁) = x∈x∷ (h₁ ∷ t)
          ∈insert-2 x h₀ h₁ t (x∈tail h₀ p) = x∈tail h₀ (x∈tail h₁ p)

  open import Proposition.Sum
  open import Data.Vec.Permutation using (_~_)

  vec-sort : (v : Vec X m) → Σₚ λ (v' : Vec X m) → v' ~ v
  vec-sort [] = [] , refl []
  vec-sort (h ∷ t)
    with vec-sort (vec-remove (find-min t h) (h ∷ t) (find-min∈ t h))
  vec-sort (h ∷ t) | v' , v'-min~h∷t =
    find-min t h ∷ v' , {!vec-remove~!}

  sort : (l : List X) → List X
  sort l = {!!} -- to-list (vec-sort (to-vec l))
  
  sort-valid : ∀ (x : X) l → x ∈ sort l ↔ x ∈ l
  ⟶ (sort-valid x l) p = {!!}
  ⟵ (sort-valid x (x ∷ t)) (x∈x∷ t) = {!!}
  ⟵ (sort-valid x (h ∷ _)) (x∈tail h q) = {!!}
  
  -- len-sort : ∀ l → len (sort l) == len l
  -- len-sort l = vec-to-list-len (vec-sort (to-vec l))

open import Operation.Binary
open import Function hiding (_$_; _~_)

module WithCommutativeSemigroup
    ⦃ sem : Semigroup X ⦄
    ⦃ com : Commutative _∙_ ⦄
    where
  Interpret :
    {Col : 𝒰 ˙}
    ⦃ _ : Collection 𝒱 Col ℕ ⦄
    (X : 𝒲 ˙)
    (t : Col)
    → --------------------------
    𝒱 ⊔ 𝒲 ˙
  Interpret X t = ∀ (x : ℕ)(p : x ∈ t) → X
  
  eval-tree : (t : BinaryTree ℕ)(values : Interpret X t) → X
  eval-tree (leaf x) values = values x (BT.∈leaf x)
  eval-tree (node l r) values = eval-tree l val-l ∙ eval-tree r val-r
    where val-l : Interpret X l
          val-l x p = values x (BT.∈left p r)
          val-r : Interpret X r
          val-r x p = values x (BT.∈right l p)

  open import Proposition.Empty

  eval-list :
    (l : NonemptyList ℕ)
    (values : Interpret X l)
    → ------------------------------
    X
  eval-list [ h ] values = values h (∈[ h ])
  eval-list (h ∷ t) values =
    values h (h ∈head t) ∙
    eval-list t (λ x p₁ → values x (x ∈⦅ h ∷ p₁ ⦆))

  eval-list-∪ : ∀ l l'
    (values : Interpret X (l ∪ l'))
    → --------------------------------
    eval-list (l ∪ l') values
    ==
    eval-list l (λ x p → values x (⟵ ∪-valid $ ∨left p)) ∙
    eval-list l' (λ x p → values x (⟵ (∪-valid {S₀ = l}) $ ∨right p))
  eval-list-∪ [ x ] l' values = refl _
  eval-list-∪ (h ∷ l) l' values =
    proof values h _ ∙ eval-list (l ∪ l') _
      === values h _ ∙ (eval-list l _ ∙ eval-list l' _)
        :by: ap (values h _ ∙_) (eval-list-∪ l l' values')
      === values h _ ∙ eval-list l _ ∙ eval-list l' _
        :by: assoc (values h _) (eval-list l _) (eval-list l' _)
    qed
    where values' : Interpret _ (l ∪ l')
          values' x p = values x (x ∈⦅ h ∷ p ⦆)

  eval-tree==eval-list :
    (t : BinaryTree ℕ)
    (values : Interpret X t)
    → ----------------------------------------------
    let values' : Interpret X (to-nonempty-list t)
        values' x p = values x (⟵ to-nonempty-list-valid p)
    in
    eval-tree t values
    ==
    eval-list (to-nonempty-list t) values'
  eval-tree==eval-list (leaf x) values = refl (values x _)
  eval-tree==eval-list (node l r) values =
    proof eval-tree l _ ∙ eval-tree r _
      === eval-list l' _ ∙ eval-list r' _
        :by: ap2 _∙_ (eval-tree==eval-list l _)
                     (eval-tree==eval-list r _)
      === eval-list (l' ∪ r') _
        :by: sym $ eval-list-∪ l' r' _
    qed
    where l' = to-nonempty-list l
          r' = to-nonempty-list r

  open import Data.NonemptyList.Permutation
    using (_~_; ∈-~)

  ~→eval-list== : ∀ {l l'}(p : l ~ l')(values : Interpret X l)
    → ----------------------------------------
    let values' : Interpret X l'
        values' x q = values x (⟵ (∈-~ x p) q)
    in
    eval-list l values == eval-list l' values'
  ~→eval-list== (_~_.refl [ x ]) values = refl (values x _)
  ~→eval-list== (_~_.refl (h ∷ l)) values =
    ap (values h (h ∈head l) ∙_)
       (~→eval-list== (_~_.refl l) λ x p → values x (x ∈⦅ h ∷ p ⦆ ))
  ~→eval-list== (_~_.trans {l₀}{l₁}{l₂} p₀ p₁) values =
    proof eval-list l₀ values
      === eval-list l₁ _
        :by: ~→eval-list== p₀ values
      === eval-list l₂ _
        :by: ~→eval-list== p₁ (λ x q → values x (⟵ (∈-~ x p₀) q))
    qed
  ~→eval-list== (_~_.swap {l₀}{l₁} x y p) values =
    proof values x _ ∙ (values y _ ∙ eval-list l₀ _)
      === values x _ ∙ values y _ ∙ eval-list l₀ _
        :by: assoc (values x _) (values y _) (eval-list l₀ _)
      === values y _ ∙ values x _ ∙ eval-list l₁ _
        :by: ap2 _∙_ (comm (values x _) (values y _))
                     (~→eval-list== p _)
      === values y _ ∙ (values x _ ∙ eval-list l₁ _)
        :by: sym $ assoc (values y _) (values x _) (eval-list l₁ _)
    qed
  ~→eval-list== (_~_.step x p) values =
    ap (values x _ ∙_) (~→eval-list== p _)

  open Sort _≤_
  open import Logic.Proof

  sort==→~ : ∀ l₀ l₁
    (p : sort (to-list l₀) == sort (to-list l₁))
    → --------------------------------------------
    l₀ ~ l₁
  sort==→~ [ x ] [ x ] (Id.refl _) = refl [ x ]
  sort==→~ (h ∷ l₀) (h₁ ∷ l₁) p = {!!}
  sort==→~ [ x ] (h ∷ t) p = {!!}
  sort==→~ (h ∷ l₀) [ x ] p = {!!}

  comm-semigroup-tactic :
    ⦃ sem : Semigroup X ⦄
    ⦃ com : Commutative (_∙_ ⦃ sem ⦄) ⦄
    (t₀ t₁ : BinaryTree ℕ)
    (p : sort (to-list t₀) == sort (to-list t₁))
    (values : Interpret X t₀)
    → -------------------------------------------
    let values' : Interpret X t₁
        values' x q = values x (⟶ (
          proof x ∈ t₁
            〉 _↔_ 〉 x ∈ to-list t₁
              :by: to-list-valid
            〉 _↔_ 〉 x ∈ sort (to-list t₁)
              :by: sym $ sort-valid x (to-list t₁)
            〉 _==_ 〉 x ∈ sort (to-list t₀)
              :by: ap (x ∈_) $ sym p 
            〉 _↔_ 〉 x ∈ to-list t₀
              :by: sort-valid x (to-list t₀)
            〉 _↔_ 〉 x ∈ t₀
              :by: sym to-list-valid
          qed)
          q)
    in eval-tree t₀ values == eval-tree t₁ values'
  comm-semigroup-tactic t₀ t₁ p values = {!!}
  -- comm-semigroup-tactic (leaf x) (leaf .x) (Id.refl _) values =
  --   refl (values x _)
  -- comm-monoid-tactic (leaf x) (node t₁ t₂) p values
  --   with antisym (∨right (s<s (z<s {0}))) (
  --     proof 2
  --       〉 _≤_ 〉 len (to-list t₁) + len (to-list t₂)
  --         :by: ap2 _+_ (tree-to-list-len t₁) (tree-to-list-len t₂)
  --       〉 _==_ 〉 len (to-list t₁ ∪ to-list t₂)
  --         :by: sym $ len++ (to-list t₁) (to-list t₂)
  --       〉 _==_ 〉 len (sort (to-list t₁ ∪ to-list t₂))
  --         :by: sym $ len-sort (to-list t₁ ∪ to-list t₂) 
  --       〉 _==_ 〉 len (sort [ x ])
  --         :by: ap len $ sym p
  --       〉 _==_ 〉 1
  --         :by: len-sort [ x ]
  --     qed)
  -- comm-monoid-tactic (leaf x) (node t₁ t₂) p values | ()
  -- comm-monoid-tactic (node t₁ t₂) (leaf x) p values
  --     with antisym (∨right (s<s (z<s {0}))) (
  --     proof 2
  --       〉 _≤_ 〉 len (to-list t₁) + len (to-list t₂)
  --         :by: ap2 _+_ (tree-to-list-len t₁) (tree-to-list-len t₂)
  --       〉 _==_ 〉 len (to-list t₁ ∪ to-list t₂)
  --         :by: sym $ len++ (to-list t₁) (to-list t₂)
  --       〉 _==_ 〉 len (sort (to-list t₁ ∪ to-list t₂))
  --         :by: sym $ len-sort (to-list t₁ ∪ to-list t₂) 
  --       〉 _==_ 〉 len (sort [ x ])
  --         :by: ap len p
  --       〉 _==_ 〉 1
  --         :by: len-sort [ x ]
  --     qed)
  -- comm-monoid-tactic (node t₀ t₁) (leaf x) p values | ()
  -- comm-monoid-tactic (node t₀ t₁) (node t₂ t₃) p values =
  --   proof eval-tree t₀ _ ∙ eval-tree t₁ _
  --     === eval-tree t₂ _ ∙ eval-tree t₃ _
  --       :by: {!!}
  --   qed
  --   where values' : Interpret X (node t₂ t₃)
  --         values' x q = values x (
  --           ⟵ to-list-valid $
  --           ⟶ (sort-valid x (to-list t₀ ∪ to-list t₁)) $
  --           Id.coe (ap (x ∈_) $ sym p) $
  --           ⟵ (sort-valid x (to-list t₂ ∪ to-list t₃)) $
  --           ⟶ to-list-valid q)

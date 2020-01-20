{-# OPTIONS --exact-split --safe --prop #-}
module Operation.Binary.Property where

open import PropUniverses as Univ
open import Operation.Binary.Definition

open import Proposition.Identity using (_==_)

record Commutative {X : 𝒰 ˙} {Y : 𝒱 ˙} (_∙_ : Op X X Y) : 𝒰 ⊔ 𝒱 ᵖ where
  field
    comm : ∀ x y → x ∙ y == y ∙ x

open Commutative ⦃ ... ⦄ public

record Associative {X : 𝒰 ˙} (_∙_ : ClosedOp X) : 𝒰 ᵖ where
  field
    assoc : ∀ x y z → x ∙ (y ∙ z) == (x ∙ y) ∙ z

open Associative ⦃ ... ⦄ public

open import Function using (flip)
open import Proof

assoc-of-flip :
  (op : Op X X X)
  ⦃ _ : Associative op ⦄
  → --------------------------
  Associative (flip op)
assoc ⦃ assoc-of-flip op ⦄ x y z = sym $ assoc z y x

swap : {_∙_ : ClosedOp X}
  ⦃ _ : Associative _∙_ ⦄
  ⦃ _ : Commutative _∙_ ⦄
  (x y z : X)
  → ------------------------
  x ∙ (y ∙ z) == y ∙ (x ∙ z)
swap {_∙_ = _∙_} x y z =
  proof x ∙ (y ∙ z)
      〉 _==_ 〉 (x ∙ y) ∙ z :by: assoc x y z
      〉 _==_ 〉 (y ∙ x) ∙ z :by: ap (_∙ z) (comm x y)
      〉 _==_ 〉 y ∙ (x ∙ z) :by: sym (assoc y x z)
  qed

record _IsLeftUnitOf_ {X : 𝒰 ˙} {Y : 𝒱 ˙} (e : X) (_∙_ : Op X Y Y) : 𝒱 ᵖ where
  field
    left-unit : ∀ y → e ∙ y == y

open _IsLeftUnitOf_ ⦃ ... ⦄ public

record _IsRightUnitOf_ {X : 𝒰 ˙} {Y : 𝒱 ˙} (e : X) (_∙_ : Op Y X Y) : 𝒱 ᵖ where
  field
    right-unit : ∀ y → y ∙ e == y

open _IsRightUnitOf_ ⦃ ... ⦄ public

open import Logic using (⊥)

record _IsUnitOf_ {X : 𝒰 ˙} (e : X) (op : Op X X X) : 𝒰 ᵖ where
  field
    ⦃ unit-left ⦄ : e IsLeftUnitOf op
    ⦃ unit-right ⦄ : e IsRightUnitOf op

open _IsUnitOf_ ⦃ ... ⦄ public

instance
  DefaultUnit :
    {e : X}{op : Op X X X}
    ⦃ _ : e IsLeftUnitOf op ⦄
    ⦃ _ : e IsRightUnitOf op ⦄
    → -------------------------
    e IsUnitOf op
  DefaultUnit = record {}

open import Proof

right-unit-of-commutative-left-unit :
  (e : X) (op : Op X X X)
  ⦃ _ : Commutative op ⦄
  ⦃ _ : e IsLeftUnitOf op ⦄
  → --------------------------
  e IsRightUnitOf op
right-unit ⦃ right-unit-of-commutative-left-unit e _∙_ ⦄ a =
  proof a ∙ e
    〉 _==_ 〉 e ∙ a :by: comm a e
    〉 _==_ 〉 a     :by: left-unit a
  qed
     
left-unit-of-commutative-right-unit :
  (e : X) (op : Op X X X)
  ⦃ _ : Commutative op ⦄
  ⦃ _ : e IsRightUnitOf op ⦄
  → --------------------------
  e IsLeftUnitOf op
left-unit ⦃ left-unit-of-commutative-right-unit e _∙_ ⦄ a =
  proof e ∙ a
    〉 _==_ 〉 a ∙ e :by: comm e a
    〉 _==_ 〉 a     :by: right-unit a
  qed

left-of-flip :
  (e : X) (op : Op X X X)
  ⦃ _ : e IsRightUnitOf op ⦄
  → --------------------------
  e IsLeftUnitOf (flip op)
left-unit ⦃ left-of-flip e op ⦄ = right-unit

right-of-flip :
  (e : X) (op : Op X X X)
  ⦃ _ : e IsLeftUnitOf op ⦄
  → --------------------------
  e IsRightUnitOf (flip op)
right-unit ⦃ right-of-flip e op ⦄ = left-unit

record LeftInverse {X : 𝒰 ˙}
    (_⁻¹ : (x : X) → X) (_∙_ : ClosedOp X) {e : X}
    ⦃ _ : e IsUnitOf _∙_ ⦄
    : --------------------------------------------
    𝒰 ᵖ where
  field
    left-inverse : ∀ x → (x ⁻¹) ∙ x == e

open LeftInverse ⦃ ... ⦄ public

record RightInverse {X : 𝒰 ˙}
    (_⁻¹ : (x : X) → X) (_∙_ : ClosedOp X) {e : X}
    ⦃ _ : e IsUnitOf _∙_ ⦄
    : --------------------------------------------
    𝒰 ᵖ where
  field
    right-inverse : ∀ x → x ∙ (x ⁻¹) == e

open RightInverse ⦃ ... ⦄ public

record Inverse {X : 𝒰 ˙}
    (_⁻¹ : (x : X) → X) (_∙_ : ClosedOp X) {e : X}
    ⦃ unit : e IsUnitOf _∙_ ⦄
    : ------------------------------------------
    𝒰 ᵖ where
  field
    ⦃ inverse-left ⦄ : LeftInverse _⁻¹ _∙_ ⦃ unit ⦄
    ⦃ inverse-right ⦄ : RightInverse _⁻¹ _∙_ ⦃ unit ⦄

open Inverse ⦃ ... ⦄ public

instance
  DefaultInverse :
    {_⁻¹ : (x : X) → X} {op : ClosedOp X} {e : X}
    ⦃ unit : e IsUnitOf op ⦄
    ⦃ _ : LeftInverse _⁻¹ op ⦃ unit ⦄ ⦄
    ⦃ _ : RightInverse _⁻¹ op ⦃ unit ⦄ ⦄
    → -----------------------------
    Inverse _⁻¹ op
  DefaultInverse = record {}

open import Relation.Binary.Definition renaming (Rel to BinRel) using ()

record Join {X : 𝒰 ˙}
    (_⊔_ : ClosedOp X) (_≼_ : BinRel 𝒱 X X)
    : --------------------------------------------
    𝒰 Univ.⊔ 𝒱 ᵖ where
  field
    ⦃ join-comm ⦄ : Commutative _⊔_
    upper-bound : ∀ x y → x ≼ (x ⊔ y)

open Join ⦃ ... ⦄ public

record Meet {X : 𝒰 ˙}
    (_⊓_ : ClosedOp X) (_≼_ : BinRel 𝒱 X X)
    : --------------------------------------------
    𝒰 ⊔ 𝒱 ᵖ where
  field
    ⦃ meet-comm ⦄ : Commutative _⊓_
    lower-bound : ∀ x y → (x ⊓ y) ≼ x

open Meet ⦃ ... ⦄ public

open import Relation.Unary renaming (Rel to UnRel) using ()

record ClosedUnder
    {X : 𝒰 ˙}
    (R : UnRel 𝒱 X)
    (_∙_ : ClosedOp X)
    : --------------------
    𝒰 ⊔ 𝒱 ˙
  where
  field
    closure : {x y : X} (p₁ : R x) (p₂ : R y) → R (x ∙ y)

open ClosedUnder ⦃ … ⦄ public

{-# OPTIONS --exact-split --prop --safe #-}
module Type.Quotient.Class where

open import PropUniverses
open import Proposition.Identity hiding (refl)
open import Relation hiding (_~_)
open import Logic
open import Function hiding (_$_; _~_)

record _/_ (X : 𝒰 ˙)(_≈_ : Bin.BinRel 𝒱 X) : 𝒰 ⊔ 𝒱 ˙ where
  field
    class-of : (x : X) → X
    class-def : ∀ {x y} → class-of x == class-of y ↔ x ≈ y
    ⦃ idempotent ⦄ : Idempotent class-of

open _/_ ⦃ … ⦄ hiding (idempotent) public

infix 19 _~_
variable
  _~_ : Bin.BinRel 𝒰 X

open import Proof hiding (sym; refl)

module QuotientRelationProperty (quot : X / _~_) where
  instance
    _ = quot
    refl-quot : Reflexive _~_
    sym-quot : Symmetric _~_
    trans-quot : Transitive _~_

  refl ⦃ refl-quot ⦄ x = ⟶ class-def $ refl (class-of x)
  sym ⦃ sym-quot ⦄ p = ⟶ class-def $ sym $ ⟵ class-def p
  trans ⦃ trans-quot ⦄ p q =
    ⟶ class-def $ trans (⟵ class-def p) (⟵ class-def q)

open import Proposition.Sum

QuotientType :
  {X : 𝒰 ˙}
  {_~_ : BinRel 𝒱 X}
  (quot : X / _~_)
  → --------------------
  𝒰 ˙
QuotientType {X = X} quot =
  Σₚ λ (x : X) → x == class-of ⦃ quot ⦄ x

as-quot :
  ⦃ quot : X / _~_ ⦄
  (x : X)
  → --------------------
  QuotientType quot
as-quot x = class-of x , sym $ idemp x

record QuotUnRel 𝒰
    {X : 𝒱 ˙}
    {_~_ : Bin.BinRel 𝒲 X}
    ⦃ quot : X / _~_ ⦄
    : -------------------------
    𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒲 ˙
    where
  field
    rel : Un.Rel 𝒰 X
    rel-preserv : ∀ {x y}(p : x ~ y) → rel x ↔ rel y

  quot-rel : Un.Rel 𝒰 (QuotientType quot)
  quot-rel (x , _) = rel x

  satisfies : ∀ {x}(p : rel x) → quot-rel (as-quot x)
  satisfies {x} p = ⟵ (rel-preserv $ ⟶ class-def $ idemp x) p

open import Operation.Binary as Op
  hiding (idemp; Idempotent)

record QuotBinOp
    {X : 𝒰 ˙}
    {_~_ : Bin.BinRel 𝒱 X}
    (quot : X / _~_)
    (_∙_ : ClosedOp X)
    : -------------------------
    𝒰 ⁺ ⊔ 𝒱 ˙
    where
  field
    preserv : ∀ {x₀ x₁ y₀ y₁}
      (p₀ : x₀ ~ x₁)
      (p₁ : y₀ ~ y₁)
      → -------------
      (x₀ ∙ y₀) ~ (x₁ ∙ y₁)

  infixl 130 _⊙_
  _⊙_ : ClosedOp (QuotientType quot)
  (x , _) ⊙ (y , _) = as-quot ⦃ quot ⦄ (x ∙ y)

open QuotBinOp ⦃ … ⦄ public using (_⊙_)

module Property
  {quot : X / _~_}
  {_∙_ : ClosedOp X}
  ⦃ q-op : QuotBinOp quot _∙_ ⦄
  where
  private
    instance _ = quot
    open QuotientRelationProperty quot
    open QuotBinOp ⦃ … ⦄ hiding (_⊙_)
    open TransMakeComposable _~_

  instance
    Commutative⊙ : ⦃ _ : Commutative _∙_ ⦄ → Commutative _⊙_
    Associative⊙ : ⦃ _ : Associative _∙_ ⦄ → Associative _⊙_
    Idempotent⊙ : ⦃ _ : Op.Idempotent _∙_ ⦄ → Op.Idempotent _⊙_
  
  assoc ⦃ Associative⊙ ⦄
    (x , _) (y , _) (z , _) =
    Σₚ== $
    ⟵ class-def (
      proof x ∙ class-of (y ∙ z)
        〉 _~_ 〉 x ∙ (y ∙ z)
          :by: preserv (refl x) $ ⟶ class-def $ idemp (y ∙ z)
        〉 _==_ 〉 (x ∙ y) ∙ z
          :by: assoc x y z
        〉 _~_ 〉 class-of (x ∙ y) ∙ z
          :by: preserv (⟶ class-def $ sym $ idemp (x ∙ y)) (refl z)
      qed)
  
  comm ⦃ Commutative⊙ ⦄ (x , _)(y , _) =
    Σₚ== $
    ⟵ class-def (
      proof x ∙ y
        〉 _~_ 〉 x ∙ y  :by: refl (x ∙ y)
        〉 _==_ 〉 y ∙ x :by: comm x y
      qed)
  
  Op.idemp ⦃ Idempotent⊙ ⦄ (x , p) = Σₚ== (
    proof class-of (x ∙ x)
      === class-of x
        :by: ap class-of $ Op.idemp x
      === x
        :by: sym p
    qed)
  
  instance
    LeftUnit⊙ :
      {one : X} ⦃ _ : one IsLeftUnitOf _∙_ ⦄
      → -------------------------------------
      as-quot one IsLeftUnitOf _⊙_
    RightUnit⊙ :
      {one : X} ⦃ _ : one IsRightUnitOf _∙_ ⦄
      → ---------------------------------------
      as-quot one IsRightUnitOf _⊙_
    LeftZero⊙ :
      {zero : X} ⦃ _ : zero IsLeftZeroOf _∙_ ⦄
      → -----------------------------------------
      as-quot zero IsLeftZeroOf _⊙_
    RightZero⊙ :
      {zero : X} ⦃ _ : zero IsRightZeroOf _∙_ ⦄
      → -----------------------------------------
      as-quot zero IsRightZeroOf _⊙_
  
  left-unit ⦃ LeftUnit⊙ {one} ⦄ (y , p) = Σₚ== (
    proof class-of (class-of one ∙ y)
      === class-of y
        :by: ⟵ class-def (
          proof class-of one ∙ y
            〉 _~_ 〉 one ∙ y
              :by: preserv (⟶ class-def $ idemp one) (refl y)
            〉 _==_ 〉 y
              :by: left-unit y
          qed)
      === y
        :by: sym p
    qed)
  
  right-unit ⦃ RightUnit⊙ {one} ⦄ (y , p) = Σₚ== (
    proof class-of (y ∙ class-of one)
      === class-of y
        :by: ⟵ class-def (
          proof y ∙ class-of one
            〉 _~_ 〉 y ∙ one
              :by: preserv (refl y) $ ⟶ class-def $ idemp one
            〉 _==_ 〉 y
              :by: right-unit y
          qed)
      === y
        :by: sym p
    qed)

  left-zero ⦃ LeftZero⊙ {zero} ⦄ (y , p) =
    Σₚ== $
    ⟵ class-def (
      proof class-of zero ∙ y
        〉 _~_ 〉 zero ∙ y
          :by: preserv (⟶ class-def $ idemp zero) (refl y)
        〉 _==_ 〉 zero
          :by: left-zero y
      qed)

  right-zero ⦃ RightZero⊙ {zero} ⦄ (y , p) =
    Σₚ== $
    ⟵ class-def (
      proof y ∙ class-of zero
        〉 _~_ 〉 y ∙ zero
          :by: preserv (refl y) $ ⟶ class-def $ idemp zero
        〉 _==_ 〉 zero
          :by: right-zero y
      qed)

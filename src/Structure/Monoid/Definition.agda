{-# OPTIONS --exact-split --safe --prop #-}
module Structure.Monoid.Definition where

open import Structure.Semigroup.Definition hiding (_∙_)

open import PropUniverses
open import Operation.Binary
  renaming (ClosedOp to Op) hiding (Op)

record FormMonoid {X : 𝒰 ˙} (_∙_ : Op X) (e : X) : 𝒰 ᵖ where
  field
    ⦃ form-semigroup ⦄ : FormSemigroup _∙_
    ⦃ unit ⦄ : e IsUnitOf _∙_

open import Proof

record Monoid (X : 𝒰 ˙) : 𝒰 ˙ where
  infixl 130 _∙_
  field
    _∙_ : Op X
    e : X
    ⦃ def ⦄  : FormMonoid _∙_ e

open Monoid ⦃ ... ⦄ public

{-# DISPLAY Monoid._∙_ M x y = _∙_ x y #-}

instance
  DefaultMonoid : {op : Op X} {e : X}
    ⦃ _ : FormSemigroup op ⦄
    ⦃ _ : e IsLeftUnitOf op ⦄
    ⦃ _ : e IsRightUnitOf op ⦄
    → -------------------
    FormMonoid op e
  DefaultMonoid = record {}

open import Function using (flip)

dual-form-monoid :
  {op : Op X} {e : X}
  ⦃ _ : FormMonoid op e ⦄
  → --------------------------
  FormMonoid (flip op) e
dual-form-monoid {op = op}{e} = record {}
  where instance
          _ = assoc-of-flip op
          _ = left-of-flip e op
          _ = right-of-flip e op

dual :
  (M : Monoid X)
  → ------------
  Monoid X
dual M = record
  { _∙_ = flip (Monoid._∙_ M)
  ; e = e
  ; def = dual-form-monoid ⦃ Monoid.def M ⦄
  }
  where instance _ = M
          

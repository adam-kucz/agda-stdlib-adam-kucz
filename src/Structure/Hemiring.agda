{-# OPTIONS --exact-split --safe --prop #-}
module Structure.Hemiring where

open import Structure.Semigroup
open import Structure.Monoid
open import Operation.Binary.Property using (Commutative)

open import PropUniverses
open import Proposition.Identity using (_==_)
open import Operation.Binary
  renaming (ClosedOp to Op) hiding (Op)

open Monoid renaming (e to zero) using ()

record FormHemiring {X : 𝒰 ˙} (_+_ _*_ : Op X) (zero : X) : 𝒰 ᵖ where
  -- TODO: figure out why this has no effect
  -- infixl 160 _⁻¹
  -- infixl 130 _∙_
  field
    ⦃ monoid+ ⦄ : FormMonoid _+_ zero
    ⦃ commutative+ ⦄ : Commutative _+_
    ⦃ semigroup* ⦄ : FormSemigroup _*_
    ⦃ 0* ⦄ : zero IsLeftZeroOf _*_
    ⦃ *0 ⦄ : zero IsRightZeroOf _*_
    *[+]==*+* : ∀ a b c → a * (b + c) == (a * b) + (a * c)
    [+]*==*+* : ∀ a b c → (a + b) * c  == (a * c) + (b * c)

open FormHemiring ⦃ ... ⦄ public

record Hemiring (X : 𝒰 ˙) : 𝒰 ˙  where
  field
    _+_ _*_ : Op X
    zero : X
    ⦃ def ⦄ : FormHemiring _+_ _*_ zero

open Hemiring ⦃ ... ⦄ public

open import Proof

binomial-sq : ∀
  {_+_ _*_ : Op X}
  {zero : X}
  ⦃ hemr : FormHemiring _+_ _*_ zero ⦄
  a b c d
  → ------------------------------------------------------------
  (a + b) * (c + d) == (((a * c) + (a * d)) + (b * c)) + (b * d)
binomial-sq {_+_ = _⊕_}{_⊗_} a b c d =
  let infixl 140 _*_; _*_ = _⊗_
      infixl 130 _+_; _+_ = _⊕_
  in
  proof (a + b) * (c + d)
    === a * (c + d) + b * (c + d)
      :by: [+]*==*+* a b (c + d)
    === a * c + a * d + b * (c + d)
      :by: ap (_+ b * (c + d)) $ *[+]==*+* a c d
    === a * c + a * d + (b * c + b * d)
      :by: ap (a * c + a * d +_) $ *[+]==*+* b c d
    === a * c + a * d + b * c + b * d
      :by: assoc _ (b * c) (b * d)
  qed
        

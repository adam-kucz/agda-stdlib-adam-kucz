{-# OPTIONS --exact-split --safe --prop #-}
module Relation.Binary.ReflexiveTransitiveClosure.Definition where

open import PropUniverses
open import Relation.Binary.Definition

data refl-trans-close {X : 𝒰 ˙}(R : BinRel 𝒱 X) : BinRel (𝒰 ⊔ 𝒱) X where
  rfl : ∀ a → refl-trans-close R a a
  step : ∀ {a b c}
    (aRb : R a b)
    (bR*c : refl-trans-close R b c)
    → -------------------------------
    refl-trans-close R a c

step-right : ∀
  {R : BinRel 𝒰 X}{a b c}
  (aR*b : refl-trans-close R a b)
  (bRc : R b c)
  → -------------------------------
  refl-trans-close R a c
step-right {c = c} (rfl a) bRc = step bRc (rfl c)
step-right (step aRb bR*b') b'Rc = step aRb (step-right bR*b' b'Rc)

-- open import Proposition.Wrapped
-- open import Data.Nat.Definition
-- open import Data.Nat.Syntax
-- open Pattern

-- len : ∀{R : BinRel 𝒰 X}{a b}
--   (aR*b : refl-trans-close R a b)
--   → ---------------------------------
--   Wrapped ℕ
-- len (rfl _) = wrap 0
-- len (step _ aR*b) with len aR*b
-- len (step _ _) | unwrap n = wrap (n +1)

{-# OPTIONS --exact-split --prop #-}
module Axiom.PropositionExtensionality where

open import PropUniverses
open import Proposition.Identity
open import Logic

postulate
  prop-ext : (p : 𝑋 ↔ 𝑌) → 𝑋 == 𝑌

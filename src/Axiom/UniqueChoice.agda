{-# OPTIONS --exact-split --prop #-}
module Axiom.UniqueChoice where

open import PropUniverses
open import Proposition.Sum using (Σₚ) 
open import Logic using (∃!) 

postulate
  !choice : {𝐴 : (x : X) → 𝒱 ᵖ} (!exists : ∃! 𝐴) → Σₚ 𝐴



{-# OPTIONS --without-K --exact-split --prop #-}
module Axiom.Choice where

open import PropUniverses
open import Prop'.Sum using (∃; Σₚ) 

postulate
  choice : {𝐴 : (x : X) → 𝒱 ᵖ} (exists : ∃ 𝐴) → Σₚ 𝐴

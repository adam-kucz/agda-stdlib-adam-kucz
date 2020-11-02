{-# OPTIONS --exact-split --safe --prop  #-}
module Logic.Basic where

open import Proposition.Unit using (⊤; ⋆ₚ) public
open import Proposition.Empty
  using (⊥; ¬_) renaming (⊥-recursionₚ to ⊥-recursion) public
open import Proposition.Sum.Definition
  using (_∧_; _,_) renaming (left to ∧left; right to ∧right) public
open import Proposition.BinarySum
  using (_∨_; ∨-contract)
  renaming (left to ∨left; right to ∨right; [_⸴_] to ∨[_⸴_])
  public


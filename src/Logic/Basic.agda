{-# OPTIONS --exact-split --safe --prop  #-}
module Logic.Basic where

open import PropUniverses
open import Proposition.Identity.Definition using (_==_; refl)

open import Proposition.Unit using (⊤; ⋆ₚ) public
open import Proposition.Empty
  using (⊥; ¬_) renaming (⊥-recursionₚ to ⊥-recursion) public
open import Proposition.Sum
  using (∃; _∧_; _,_) renaming (left to ∧left; right to ∧right) public
open import Proposition.BinarySum
  using (_∨_; ∨-contract)
  renaming (left to ∨left; right to ∨right; [_⸴_] to ∨[_⸴_])
  public

∃! : {X : 𝒰 ˙} (𝐴 : (x : X) → 𝒱 ᵖ) → 𝒰 ⊔ 𝒱 ᵖ
∃! {X = X} 𝐴 = ∃ λ (x : X) → 𝐴 x ∧ ∀ y (p : 𝐴 y) → y == x


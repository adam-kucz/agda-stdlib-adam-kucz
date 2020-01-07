{-# OPTIONS --exact-split --safe --prop  #-}
module Logic where

open import PropUniverses
open import Proposition.Identity.Definition using (_==_; refl)

open import Proposition.Unit using (⊤; ⋆ₚ) public
open import Proposition.Empty
  using (⊥; ¬_) renaming (⊥-recursionₚ to ⊥-recursion) public
open import Proposition.Sum
  using (∃; _∧_; _,_) renaming (left to ∧left; right to ∧right) public
open import Proposition.BinarySum
  using (_∨_; ∨-contract) renaming (left to ∨left; right to ∨right) public

∃! : {X : 𝒰 ˙} (𝐴 : (x : X) → 𝒱 ᵖ) → 𝒰 ⊔ 𝒱 ᵖ
∃! {X = X} 𝐴 = ∃ λ (x : X) → 𝐴 x ∧ ∀ y (p : 𝐴 y) → y == x

infix 11 _↔_
infixl 11 _,_
record _↔_ (𝑋 : 𝒰 ᵖ) (𝑌 : 𝒱 ᵖ) : 𝒰 ⊔ 𝒱 ᵖ where
  constructor _,_
  field
    ⟶ : (p : 𝑋) → 𝑌
    ⟵ : (q : 𝑌) → 𝑋

open _↔_ public

==→↔ :
  {𝑋 𝑌 : 𝒰 ᵖ}
  (p : 𝑋 == 𝑌)
  → -------------------
  𝑋 ↔ 𝑌
==→↔ (refl x) = id , id
  where id = λ p → p

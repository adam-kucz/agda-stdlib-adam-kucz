{-# OPTIONS --exact-split --safe --prop  #-}
module Logic.Iff where

open import PropUniverses
open import Proposition.Identity.Definition using (_==_; refl)

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

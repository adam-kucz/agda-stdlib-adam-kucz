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
  (p : 𝑋 == 𝑌)
  → -------------------
  𝑋 ↔ 𝑌
==→↔ (refl x) = id , id
  where id = λ p → p

open import Proposition.Empty

-↔-→¬↔¬ : 
  (p : 𝑋 ↔ 𝑌)
  → -------------------
  ¬ 𝑋 ↔ ¬ 𝑌
-↔-→¬↔¬ (X→Y , Y→X) =
  (λ ¬X Y → ¬X (Y→X Y)) ,
  (λ ¬Y X → ¬Y (X→Y X))

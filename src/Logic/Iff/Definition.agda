{-# OPTIONS --exact-split --safe  #-}
module Logic.Iff.Definition where

open import Universes
open import Type.Identity.Definition using (_==_; refl)

infix 11 _↔_
infixl 11 _,_
record _↔_ (𝑋 : 𝒰 ˙)(𝑌 : 𝒱 ˙) : 𝒰 ⊔ 𝒱 ˙ where
  constructor _,_
  field
    ⟶ : (p : 𝑋) → 𝑌
    ⟵ : (q : 𝑌) → 𝑋

open _↔_ public

==→↔ :
  (p : X == Y)
  → -------------------
  X ↔ Y
==→↔ (refl x) = id , id
  where id = λ p → p

open import Type.Empty

-↔-→¬↔¬ : 
  (p : X ↔ Y)
  → -------------------
  ¬ X ↔ ¬ Y
-↔-→¬↔¬ (X→Y , Y→X) =
  (λ ¬X Y → ¬X (Y→X Y)) ,
  (λ ¬Y X → ¬Y (X→Y X))

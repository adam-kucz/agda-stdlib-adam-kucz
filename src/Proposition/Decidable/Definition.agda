{-# OPTIONS --exact-split --safe --prop  #-}
module Proposition.Decidable.Definition where

open import PropUniverses
open import Logic.Basic
open import Proposition.Function using (_$_)

data Decidable (𝑋 : 𝒰 ᵖ) : 𝒰 ˙ where
  true : (p : 𝑋) → Decidable 𝑋
  false : (¬p : ¬ 𝑋) → Decidable 𝑋

decide : (𝑋 : 𝒰 ᵖ) ⦃ d : Decidable 𝑋 ⦄ → Decidable 𝑋
decide 𝑋 ⦃ d ⦄ = d

if_:by:_then_else_ :
  (𝑋 : 𝒰 ᵖ)
  (d : Decidable 𝑋)
  (x y : X)
  → --------------------
  X
if 𝑋 :by: d then x else y with decide 𝑋 ⦃ d ⦄
if 𝑋 :by: d then x else y | true _ = x
if 𝑋 :by: d then x else y | false _ = y

if_then_else_ :
  (𝑋 : 𝒰 ᵖ)
  ⦃ d : Decidable 𝑋 ⦄
  (x y : X)
  → --------------------
  X
if 𝑋 then x else y with decide 𝑋
if 𝑋 then x else y | true _ = x
if 𝑋 then x else y | false _ = y

dif_then_else_ :
  (𝑋 : 𝒰 ᵖ)
  ⦃ d : Decidable 𝑋 ⦄
  (f : (p : 𝑋) → X)
  (g : (¬p : ¬ 𝑋) → X )
  → --------------------
  X
dif 𝑋 then f else g with decide 𝑋
dif 𝑋 then f else g | true p = f p
dif 𝑋 then f else g | false ¬p = g ¬p

_by-difₚ_then_else_ :
  (𝐴 : (x : X) → 𝒱 ᵖ)
  (𝑋 : 𝒰 ᵖ)
  ⦃ d : Decidable 𝑋 ⦄
  {x y : X}
  (f : (p : 𝑋) → 𝐴 x)
  (g : (¬p : ¬ 𝑋) → 𝐴 y)
  → --------------------
  𝐴 (if 𝑋 then x else y)
_by-difₚ_then_else_ 𝐴 𝑋 ⦃ d ⦄ f g with decide 𝑋 ⦃ d ⦄
_ by-difₚ 𝑋 then f else g | true p = f p
_ by-difₚ 𝑋 then f else g | false ¬p = g ¬p

instance
  ⊥Decidable : Decidable ⊥
  ⊤Decidable : Decidable ⊤
  LiftDecidable : ⦃ d : Decidable 𝑋 ⦄ → Decidable (Lift𝒰ᵖ {𝒱 = 𝒰} 𝑋)
  ¬Decidable : ⦃ p : Decidable 𝑋 ⦄ → Decidable (¬ 𝑋)
  ∨Decidable : ⦃ p : Decidable 𝑋 ⦄ ⦃ q : Decidable 𝑌 ⦄ → Decidable (𝑋 ∨ 𝑌)
  ∧Decidable : ⦃ p : Decidable 𝑋 ⦄ ⦃ q : Decidable 𝑌 ⦄ → Decidable (𝑋 ∧ 𝑌)
  →Decidable : ⦃ p : Decidable 𝑋 ⦄ ⦃ q : Decidable 𝑌 ⦄ → Decidable (𝑋 → 𝑌)

⊥Decidable = false λ ()

⊤Decidable = true ⋆ₚ
  
LiftDecidable ⦃ d = true p ⦄ = true (↑prop p)
LiftDecidable ⦃ d = false ¬p ⦄ = false (λ z → ¬p (↓prop z))
  
¬Decidable ⦃ true p ⦄ = false λ ¬p → ¬p p
¬Decidable ⦃ false ¬p ⦄ = true ¬p

∨Decidable ⦃ true p ⦄ ⦃ q ⦄ = true (∨left p)
∨Decidable ⦃ false ¬p ⦄ ⦃ true q ⦄ = true (∨right q)
∨Decidable ⦃ false ¬p ⦄ ⦃ false ¬q ⦄ =
  false λ { (∨left p) → ¬p p ; (∨right q) → ¬q q}

∧Decidable ⦃ false ¬p ⦄ ⦃ q ⦄ = false λ p∧q → ¬p $ ∧left p∧q
∧Decidable ⦃ true p ⦄ ⦃ false ¬q ⦄ = false λ p∧q → ¬q $ ∧right p∧q
∧Decidable ⦃ true p ⦄ ⦃ true q ⦄ = true (p , q)

→Decidable {𝑌 = 𝑌} ⦃ false ¬p ⦄ ⦃ q ⦄ = true λ p → ⊥-recursion 𝑌 (¬p p)
→Decidable ⦃ true p ⦄ ⦃ true q ⦄ = true λ _ → q
→Decidable ⦃ true p ⦄ ⦃ false ¬q ⦄ = false λ p→q → ¬q $ p→q p

open import Logic.Iff

instance
  ↔Decidable : ⦃ p : Decidable 𝑋 ⦄ ⦃ q : Decidable 𝑌 ⦄ → Decidable (𝑋 ↔ 𝑌)

↔Decidable ⦃ true p ⦄ ⦃ true q ⦄ = true ((λ p → q) , (λ q → p))
↔Decidable ⦃ true p ⦄ ⦃ false ¬q ⦄ = false (λ z → ¬q (_↔_.⟶ z p))
↔Decidable ⦃ false ¬p ⦄ ⦃ true q ⦄ = false (λ z → ¬p (_↔_.⟵ z q))
↔Decidable {𝑋 = 𝑋} {𝑌 = 𝑌} ⦃ false ¬p ⦄ ⦃ false ¬q ⦄ =
  true ((λ p → ⊥-recursion 𝑌 (¬p p)) ,
        (λ q → ⊥-recursion 𝑋 (¬q q)))

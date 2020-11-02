{-# OPTIONS --exact-split --safe --prop  #-}
module Logic.Exists where

open import PropUniverses
open import Proposition.Identity.Definition using (_==_; refl)
open import Proposition.Sum.Definition
  using (_∧_; _,_) renaming (left to ∧left; right to ∧right)
open import Proposition.Sum.Definition using (∃; _,_) public

open import Logic.Iff

∃! : {X : 𝒰 ˙} (𝐴 : (x : X) → 𝒱 ᵖ) → 𝒰 ⊔ 𝒱 ᵖ
∃! {X = X} 𝐴 = ∃ λ (x : X) → 𝐴 x ∧ ∀ y (p : 𝐴 y) → y == x

↔→∃!↔∃! : (p : ∀ x → 𝐴 x ↔ 𝐵 x) → ∃! 𝐴 ↔ ∃! 𝐵
⟶ (↔→∃!↔∃! p) (x , (pa , !)) = x , (⟶ (p x) pa , λ y pb → ! y (⟵ (p y) pb))
⟵ (↔→∃!↔∃! p) (x , (pb , !)) = x , (⟵ (p x) pb , λ y pa → ! y (⟶ (p y) pa))

∃!-of-type : (X : 𝒰 ˙) → 𝒰 ᵖ
∃!-of-type X = ∃ λ (x : X) → ∀ y → y == x

∃!== : ∀(!A : ∃! 𝐴){x y}(p : 𝐴 x)(q : 𝐴 y) → x == y
∃!== (z , (_ , !z)) {x}{y} p q with refl z ← !z x p | refl z ← !z y q = refl z

∃!-of-type== : (!X : ∃!-of-type X)(x y : X) → x == y
∃!-of-type== (z , !X) x y with refl z ← !X x | refl z ← !X y = refl z

∃!→∃ : (!A : ∃! 𝐴) → ∃ 𝐴
∃!→∃ (x , (p , _)) = x , p

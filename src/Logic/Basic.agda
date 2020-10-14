{-# OPTIONS --exact-split --safe  #-}
module Logic.Basic where

open import Universes
open import Type.Identity.Definition using (_==_; refl)

open import Type.Unit using (⋆) renaming (𝟙 to ⊤) public
open import Type.Empty
  using (¬_) renaming (𝟘 to ⊥; 𝟘-recursion to ⊥-recursion) public
open import Type.Sum.Definition
  using (_,_)
  renaming (_×_ to infixl 17 _∧_; pr₁ to ∧left; pr₂ to ∧right)
  public
open import Type.Sum.Definition
  using ()
  renaming (Σ to ∃; pr₁ to elem; pr₂ to prop)
  public
open import Type.BinarySum.Definition
  using ([_+_]; [_,_])
  renaming (_+_ to infixl 15 _∨_; left to ∨left; right to ∨right)
  public

∃! : {X : 𝒰 ˙} (𝐴 : (x : X) → 𝒱 ˙) → 𝒰 ⊔ 𝒱 ˙
∃! {X = X} 𝐴 = ∃ λ (x : X) → 𝐴 x ∧ ∀ y (p : 𝐴 y) → y == x

infixl 17 _∧ᵈ_
_∧ᵈ_ : (P : 𝒰 ˙)(A : (p : P) → 𝒱 ˙) → 𝒰 ⊔ 𝒱 ˙
P ∧ᵈ A = ∃ {X = P} A

infixl 15 _⊻_
_⊻_ : (X : 𝒰 ˙)(Y : 𝒱 ˙) → 𝒰 ⊔ 𝒱 ˙
X ⊻ Y = (X ∨ Y) ∧ ¬ (X ∧ Y)

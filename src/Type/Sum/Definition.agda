{-# OPTIONS --exact-split --safe --prop #-}
module Type.Sum.Definition where

open import Universes

infixl 51 _,_
record Σ {X : 𝒰 ˙} (A : (x : X) → 𝒱 ˙) : 𝒰 ⊔ 𝒱 ˙ where
  constructor _,_
  field
    pr₁ : X
    pr₂ : A pr₁

infixl 57 _×_
_×_ : (X : 𝒰 ˙) (Y : 𝒱 ˙) → 𝒰 ⊔ 𝒱 ˙
X × Y = Σ λ (_ : X) → Y

open Σ public

mk-Σ-implicit : {x : X}(y : A x) → Σ A
mk-Σ-implicit {x = x} y = x , y

Σ-assoc : 
  {K : (x : X)(y : A x) → 𝒰 ˙}
  (σ : Σ λ (x : X) → Σ (K x))
  → -------------------------
  Σ λ (xy : Σ A) → K (pr₁ xy) (pr₂ xy)
Σ-assoc (x , (y , z)) = ((x , y), z)

〈_,_〉 :
  (f : (x : X) → Y)
  (g : (x : X) → Z)
  → -----------------------
  (x : X) → Y × Z
〈 f , g 〉 x = f x , g x

〈_×_〉 :
  (f : (x : X₀) → X₁)
  (g : (y : Y₀) → Y₁)
  → -----------------------
  (xy : X₀ × Y₀) → X₁ × Y₁
〈 f × g 〉 (x , y) = f x , g y

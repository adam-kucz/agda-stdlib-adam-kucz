{-# OPTIONS --without-K --exact-split --safe #-}
module Type.Empty where

open import Universes

data 𝟘 : 𝒰₀ ˙ where

𝟘-induction : (A : (p : 𝟘) → 𝒰 ˙) (p : 𝟘) → A p
𝟘-induction _ ()

𝟘-recursion : (X : 𝒰 ˙) (p : 𝟘) → X
𝟘-recursion _ ()

infix 18 ¬_ 
¬_ : (𝑋 : 𝒰 ˙) → 𝒰 ˙
¬ X = X → 𝟘

empty : (X : 𝒰 ˙) → 𝒰 ˙
empty X = X → 𝟘

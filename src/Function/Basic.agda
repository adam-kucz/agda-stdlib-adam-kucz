{-# OPTIONS --exact-split --safe #-}
module Function.Basic where

open import Universes
open import Type.Product public

id : (x : X) → X
id x = x
  
𝑖𝑑 : (X : 𝒰 ˙) (x : X) → X
𝑖𝑑 X = id

domain : {X : 𝒰 ˙} {A : (x : X) → 𝒱 ˙}
  (f : (x : X) → A x)
  → -----------------
  𝒰 ˙
domain {X = X} _ = X

codomain : {X : 𝒰 ˙} {Y : 𝒱 ˙}
  (f : (x : X) → Y)
  → -----------------
  𝒱 ˙
codomain {Y = Y} _ = Y

type-of : {X : 𝒰 ˙} (x : X) → 𝒰 ˙
type-of {X = X} _ = X

universe-of : (X : 𝒰 ˙) → Universe
universe-of {𝒰} _ = 𝒰

open import Type.Sum.Definition

uncurry : {K : (x : X)(y : A x) → 𝒰 ˙}
  (f : (x : X)(y : A x) → K x y)
  → ---------------------------
  (xy : Σ A) → K (pr₁ xy) (pr₂ xy)
uncurry f (x , y) = f x y

infixr 16 _$_
_$_ : {A : 𝒰 ˙} {B : A → 𝒱 ˙}
  (f : (x : A) → B x)
  (x : A)
  → -----------------------
  B x
f $ x = f x

{-# DISPLAY _$_ f x = f x #-}

infixl 150 _∘_ _∘ₛ_
_∘_ :
  {K : (x : X) (y : A x) → 𝒲 ˙}
  (f : {x : X} (y : A x) → K x y)
  (g : (x : X) → A x)
  → ----------------------------
  (x : X) → K x (g x)
(f ∘ g) x = f (g x)

_∘ₛ_ : (g : Y → Z)(f : X → Y) → (X → Z)
g ∘ₛ f = g ∘ f

flip :
  {K : (x : X) (y : Y) → 𝒲 ˙}
  (f : (x : X) (y : Y) → K x y)
  → ---------------------------
  (y : Y)(x : X) → K x y
flip f y x = f x y

open import Data.Nat.Definition
open import Data.Nat.Syntax
open Pattern

repeat : (f : X → X)(m : ℕ)(x : X) → X
repeat f 0 x = x
repeat f (m +1) x = f $ repeat f m x

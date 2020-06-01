{-# OPTIONS --exact-split --prop #-}
module Axiom.FunctionExtensionality where

open import PropUniverses
open import Proposition.Identity.Heterogeneous using (_==_)
open import Function.Equivalence

postulate
  fun-ext :
    {f : (x : X) → A x}
    {f' : (x : X) → B x}
    (equiv : f ~ f')
    → ----------------------------
    f == f'

  fun-ext-implicit :
    {f : {x : X} → A x}
    {f' : {x : X} → B x}
    (equiv : (λ x → f {x}) ~ (λ x → f' {x}))
    → ----------------------------------------
    (λ {x} → f {x}) == (λ {x} → f' {x})

  fun-extₚ : {A B : 𝑋 → 𝒰 ˙}
    {f : (x : 𝑋) → A x}
    {f' : (x : 𝑋) → B x}
    (equiv : (x : 𝑋) → f x == f' x)
    → -------------------------------
    f == f'

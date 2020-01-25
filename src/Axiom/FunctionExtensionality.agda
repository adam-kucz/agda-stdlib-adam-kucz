{-# OPTIONS --exact-split --prop #-}
module Axiom.FunctionExtensionality where

open import Universes
open import Proposition.Identity using (_==_)
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


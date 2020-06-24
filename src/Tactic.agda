{-# OPTIONS --exact-split --safe --prop  #-}
module Tactic where

open import Universes
-- open import Agda.Builtin.Unit
open import Tactic.Reflection

default : (x : X) → Term → TC ⊤
default x hole = bindTC (quoteTC x) (unify hole)


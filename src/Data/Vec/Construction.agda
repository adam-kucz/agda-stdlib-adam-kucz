{-# OPTIONS --safe --exact-split --prop  #-}
module Data.Vec.Construction where

open import Data.Vec.Definition
open import Data.Vec.Function

open import Data.Nat

enum-from_for_ : (m n : ℕ) → Vec ℕ n
enum-from m for 0 = []
enum-from m for (n +1) = m ∷ (enum-from m +1 for n)

upto< : (n : ℕ) → Vec ℕ n
upto< = enum-from 0 for_

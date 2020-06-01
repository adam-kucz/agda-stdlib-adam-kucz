{-# OPTIONS --safe --exact-split --prop  #-}
module Data.Tree.Binary.Definition where

open import Universes

data BinaryTree (X : 𝒰 ˙) : 𝒰 ˙ where
  leaf : (x : X) → BinaryTree X
  branch : (l r : BinaryTree X) → BinaryTree X

infixr 115 _/\_
pattern _/\_ l r = branch l r

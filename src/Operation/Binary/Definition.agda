{-# OPTIONS --exact-split --safe --prop #-}
module Operation.Binary.Definition where

open import PropUniverses

Op : (X : 𝒰 ˙) (Y : 𝒱 ˙) (Z : 𝒲 ˙) → 𝒰 ⊔ 𝒱 ⊔ 𝒲 ˙
Op X Y Z = (x : X) (y : Y) → Z

ClosedOp : (X : 𝒰 ˙) → 𝒰 ˙
ClosedOp X = Op X X X

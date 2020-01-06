{-# OPTIONS --exact-split --prop  #-}
module Function.Extensionality where

open import Universes
open import Prop'.Identity using (_==_)

postulate
  fun-ext :
    {f : (x : X) → A x}
    {f' : (x : X) → B x}
    (ext : (x : X) → f x == f' x)
    → ----------------------
    f == f'
    

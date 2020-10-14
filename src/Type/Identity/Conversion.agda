{-# OPTIONS --exact-split --safe #-}
module Type.Identity.Conversion where

open import Universes

import Type.Identity.Homogeneous.Definition as Hom
import Type.Identity.Heterogeneous.Definition as Het

==→het== : {x y : X}(p : x Hom.== y) → x Het.== y
==→het== (Hom.refl a) = Het.refl a

het==→== : {x y : X}(p : x Het.== y) → x Hom.== y
het==→== (Het.refl x) = Hom.refl x

{-# OPTIONS --exact-split --safe --prop #-}
module Proposition.Identity.Conversion where

open import Universes

import Proposition.Identity.Homogeneous.Definition as Hom
import Proposition.Identity.Heterogeneous.Definition as Het

==→het== : {x y : X}(p : x Hom.== y) → x Het.== y
==→het== (Hom.refl a) = Het.refl a

het==→== : {x y : X}(p : x Het.== y) → x Hom.== y
het==→== (Het.refl x) = Hom.refl x

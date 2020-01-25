{-# OPTIONS --exact-split --safe --prop #-}
module Proposition.Identity.Property where

open import PropUniverses
open import Relation.Binary.Property as Rel
  renaming (refl to rel-refl; sym to rel-sym)
open import Proposition.Identity.Definition

instance
  Transitive== : Transitive {𝒱 = 𝒱} {X = X} _==_
  trans ⦃ Transitive== ⦄ p (refl x) = p

  Reflexive== : Reflexive {𝒱 = 𝒱} {X = X} _==_
  rel-refl ⦃ Reflexive== ⦄ = refl

  Symmetric== : Symmetric {𝒱 = 𝒱} {X = X} _==_
  rel-sym ⦃ Symmetric== ⦄ (refl x) = refl x
  
  Equivalence== : Equivalence {𝒱 = 𝒱} {X = X} _==_
  equiv-reflexive ⦃ Equivalence== ⦄ = Reflexive==
  equiv-symmetric ⦃ Equivalence== ⦄ = Symmetric==
  equiv-transitive ⦃ Equivalence== ⦄ = Transitive==

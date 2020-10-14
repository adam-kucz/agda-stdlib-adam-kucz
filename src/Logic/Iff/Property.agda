{-# OPTIONS --exact-split --safe  #-}
module Logic.Iff.Property where

open import Logic.Iff.Definition

open import Universes
open import Relation.Binary

instance
  Reflexive↔ : Reflexive (_↔_ {𝒰})
  Transitive↔ : Transitive (_↔_ {𝒰})
  Symmetric↔ : Symmetric (_↔_ {𝒰})

open import Function.Basic

refl ⦃ Reflexive↔ ⦄ _ = id , id
trans ⦃ Transitive↔ ⦄ (𝑋→𝑌 , 𝑌→𝑋) (𝑌→𝑍 , 𝑍→𝑌) = 𝑌→𝑍 ∘ 𝑋→𝑌 , 𝑌→𝑋 ∘ 𝑍→𝑌
sym ⦃ Symmetric↔ ⦄ (𝑋→𝑌 , 𝑌→𝑋) = (𝑌→𝑋 , 𝑋→𝑌)

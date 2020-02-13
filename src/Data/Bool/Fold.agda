{-# OPTIONS --exact-split --prop #-}
module Data.Bool.Fold where

open import Data.Bool.Definition
open import Data.Bool.Monoid
open import Data.Bool.Correspondence

open import PropUniverses
open import Proposition.Decidable as Dec hiding (true; false)
open import Type.Sum hiding (_,_) 
open import Proposition.Sum.Monoid
open import Structure.Monoid
open import Data.Collection
open import Data.Collection.Listable.Function
open import Data.Functor
open import Data.List
open import Data.List.Functor
open import Logic
open import Proof

fold-to-bool : {Col : 𝒰 ˙}
  ⦃ list : Listable 𝒲 Col (Σ λ (𝑋 : 𝒱 ᵖ) → Decidable 𝑋) ⦄
  ⦃ monᵖ : Monoid (𝒱 ᵖ) ⦄
  ⦃ monBool : Monoid Bool ⦄
  (p : e <~> e)
  (q : _∙_ <~2~> _∙_)
  (S : Col)
  → --------------------------------------
  fold-map pr₁ ⦃ monᵖ ⦄ S
  <~>
  fold-map (λ {(𝑋 Σ., d) → to-bool 𝑋 ⦃ d ⦄}) ⦃ monBool ⦄ S
fold-to-bool {𝒱 = 𝒱} ⦃ monᵖ = monᵖ ⦄ ⦃ monBool ⦄ p q S = go p q (to-list S)
  where go :
          (p : e <~> e)
          (q : _∙_ <~2~> _∙_)
          (l : List (Σ λ (𝑋 : 𝒱 ᵖ) → Decidable 𝑋))
          → ----------------------------------------------------------------------
          mconcat ⦃ monᵖ ⦄ (pr₁ <$> l)
          <~>
          mconcat ⦃ monBool ⦄ ((λ {(𝑋 Σ., d) → to-bool 𝑋 ⦃ d ⦄}) <$> l)
        go p q []  = p
        go p q ((𝑋 Σ., d) ∷ t) = 
          q 𝑋 (to-bool 𝑋 ⦃ d ⦄) (d , refl _)
            (mconcat (pr₁ <$> t))
            (mconcat ((λ {(𝑋 Σ., d) → to-bool 𝑋 ⦃ d ⦄}) <$> t))
            (go p q t)

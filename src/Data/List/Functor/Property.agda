{-# OPTIONS --exact-split  #-}
module Data.List.Functor.Property where

open import Data.List.Functor.Definition

open import Universes
open import Data.Functor
open import Data.List hiding (_++_)
open import Collection
open import Logic
open import Proof
import Data.List.Insertable
import Data.List.Property

open import Data.Monad

fmap-++ : {X : 𝒰 ˙}{Y : 𝒱 ˙}
  (f : X → Y)(l l' : List X)
  → ---------------------------------------
  f <$> l ++ l' == (f <$> l) ++ (f <$> l')
fmap-++ f l [] = refl (f <$> l)
fmap-++ f l (h ∷ t) = ap (f h ∷_) $ fmap-++ f l t

open import Structure.Monoid

∈bind : {X : 𝒰 ˙}{Y : 𝒱 ˙}
  (x : X)
  (f : Y → List X)
  (l : List Y)
  → --------------------------------------------------
  x ∈ (l >>= f) ↔ ∃ λ y → y ∈ l ∧ x ∈ f y
⟶ (∈bind x f l) p with ⟶ (∈mconcat (fmap f l) x) p
⟶ (∈bind x f l) p | y' , (y'∈fmap , x∈y) with ∈map⁻¹ l f y'∈fmap
⟶ (∈bind x f l) p | .(f y) , (_ , x∈fy) | y , (Id.refl _ , y∈l) =
  y , (y∈l , x∈fy)
⟵ (∈bind x f l) (y , (y∈l , x∈fy)) =
  ⟵ (∈mconcat (fmap f l) x) $
  (f y , (∈map f y∈l , x∈fy))

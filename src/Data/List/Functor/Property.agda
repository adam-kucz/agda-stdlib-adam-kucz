{-# OPTIONS --exact-split --prop  #-}
module Data.List.Functor.Property where

open import Data.List.Functor.Definition

open import Universes
open import Data.Functor
open import Data.List hiding (_++_)
open import Collection
open import Proof

∈fmap :
  {X : 𝒰 ˙}{Y : 𝒱 ˙}
  {x : X}{l : List X}
  (f : (x : X) → Y)
  (p : x ∈ l)
  → ------------------
  f x ∈ (f <$> l)
∈fmap f (x∈x∷ t) = x∈x∷ f <$> t
∈fmap f (x∈tail h p) = x∈tail (f h) (∈fmap f p)

open import Logic

∈fmap⁻¹ : 
  {X : 𝒰 ˙}{Y : 𝒱 ˙}
  {y : Y}
  (l : List X)
  (f : (x : X) → Y)
  (p : y ∈ (f <$> l))
  → ------------------
  ∃ λ (x : X) → f x == y ∧ x ∈ l
∈fmap⁻¹ (h ∷ l) f (x∈x∷ .(f <$> l)) =
  h , (Id-refl (f h) , x∈x∷ l)
∈fmap⁻¹ (h ∷ l) f (x∈tail .(f h) p) with ∈fmap⁻¹ l f p
∈fmap⁻¹ (h ∷ l) f (x∈tail .(f h) p) | x , (fx==y , x∈l) =
  x , (fx==y , x∈tail h x∈l)

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
⟶ (∈bind x f l) p | y' , (y'∈fmap , x∈y) with ∈fmap⁻¹ l f y'∈fmap
⟶ (∈bind x f l) p | .(f y) , (_ , x∈fy) | y , (Id-refl _ , y∈l) =
  y , (y∈l , x∈fy)
⟵ (∈bind x f l) (y , (y∈l , x∈fy)) =
  ⟵ (∈mconcat (fmap f l) x) $
  (f y , (∈fmap f y∈l , x∈fy))

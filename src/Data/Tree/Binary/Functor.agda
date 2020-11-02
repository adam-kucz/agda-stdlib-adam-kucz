{-# OPTIONS --exact-split --prop  #-}
module Data.Tree.Binary.Functor where

open import Data.Tree.Binary.Definition
open import Data.Tree.Binary.Function

open import Universes
open import Data.Functor
open import Data.Applicative
open import Data.Monad
open import Function
  renaming (_∘ₛ_ to _∘_; _$_ to _$'_)
  using (universe-of; uncurry; id; 𝑖𝑑; ==→~; _~_)
open import Proof

instance
  BinaryTreeFunctor : Functor {U = universe-of} (λ X → BinaryTree X)
  BinaryTreeApplicative : Applicative {U = universe-of} (λ X → BinaryTree X)
  BinaryTreeMonad : Monad {U = universe-of} (λ X → BinaryTree X)

open import Axiom.FunctionExtensionality

fmap ⦃ BinaryTreeFunctor ⦄ = map
fmap-id ⦃ BinaryTreeFunctor ⦄ = subrel $ fun-ext go
  where go : map (𝑖𝑑 X) ~ id
        go (leaf x) = Het.refl (leaf x)
        go (l /\ r) = ap2 _/\_ (go l) (go r)  
fmap-∘ ⦃ BinaryTreeFunctor ⦄ g f = subrel {sup = _==_} $ fun-ext go
  where go : map (g ∘ f) ~ map g ∘ map f
        go (leaf x) = Het.refl (leaf (g (f x)))
        go (l /\ r) = ap2 _/\_ (go l) (go r)  

open import Type.Unit
open import Type.Sum

functor ⦃ BinaryTreeApplicative ⦄ = BinaryTreeFunctor
unit ⦃ BinaryTreeApplicative ⦄ = leaf ⋆
_⋆_ ⦃ BinaryTreeApplicative ⦄ (leaf x) = map (x ,_)
_⋆_ ⦃ BinaryTreeApplicative ⦄ (l /\ r) y =
  _⋆_ ⦃ BinaryTreeApplicative ⦄ l y /\
  _⋆_ ⦃ BinaryTreeApplicative ⦄ r y
fmap-def ⦃ BinaryTreeApplicative ⦄ f (leaf x) = Id.refl (leaf (f x))
fmap-def ⦃ BinaryTreeApplicative ⦄ f (l /\ r) =
  ap2 _/\_ (fmap-def ⦃ BinaryTreeApplicative ⦄ f l)
           (fmap-def ⦃ BinaryTreeApplicative ⦄ f r)
naturality ⦃ BinaryTreeApplicative ⦄ f g (leaf x) (leaf x') =
  Id.refl (leaf (f x , g x'))
naturality ⦃ BinaryTreeApplicative ⦄ f g (leaf x) (l' /\ r') =
  ap2 _/\_ (naturality ⦃ BinaryTreeApplicative ⦄ f g (leaf x) l')
           (naturality ⦃ BinaryTreeApplicative ⦄ f g (leaf x) r')
naturality ⦃ BinaryTreeApplicative ⦄ f g (l /\ r) v =
  ap2 _/\_ (naturality ⦃ BinaryTreeApplicative ⦄ f g l v)
           (naturality ⦃ BinaryTreeApplicative ⦄ f g r v)
left-identity ⦃ BinaryTreeApplicative ⦄ (leaf x) = Id.refl (leaf x)
left-identity ⦃ BinaryTreeApplicative ⦄ (l /\ r) =
  ap2 _/\_ (left-identity ⦃ BinaryTreeApplicative ⦄ l)
           (left-identity ⦃ BinaryTreeApplicative ⦄ r)
right-identity ⦃ BinaryTreeApplicative ⦄ (leaf x) = Id.refl (leaf x)
right-identity ⦃ BinaryTreeApplicative ⦄ (l /\ r) =
  ap2 _/\_ (right-identity ⦃ BinaryTreeApplicative ⦄ l)
           (right-identity ⦃ BinaryTreeApplicative ⦄ r)
⋆-assoc ⦃ BinaryTreeApplicative ⦄ (leaf x) (leaf x') (leaf x″) =
  Id.refl (leaf (x , x' , x″))
⋆-assoc ⦃ BinaryTreeApplicative ⦄ (leaf x) (leaf x') (l″ /\ r″) =
  ap2 _/\_ (⋆-assoc ⦃ BinaryTreeApplicative ⦄ (leaf x) (leaf x') l″)
           (⋆-assoc ⦃ BinaryTreeApplicative ⦄ (leaf x) (leaf x') r″)
⋆-assoc ⦃ BinaryTreeApplicative ⦄ (leaf x) (l' /\ r') w =
  ap2 _/\_ (⋆-assoc ⦃ BinaryTreeApplicative ⦄ (leaf x) l' w)
           (⋆-assoc ⦃ BinaryTreeApplicative ⦄ (leaf x) r' w)
⋆-assoc ⦃ BinaryTreeApplicative ⦄ (l /\ r) v w =
  ap2 _/\_ (⋆-assoc ⦃ BinaryTreeApplicative ⦄ l v w)
           (⋆-assoc ⦃ BinaryTreeApplicative ⦄ r v w)

private
  t-join : BinaryTree (BinaryTree X) → BinaryTree X
t-join (leaf x) = x
t-join (l /\ r) = t-join l /\ t-join r

applicative ⦃ BinaryTreeMonad ⦄ = BinaryTreeApplicative
join ⦃ BinaryTreeMonad ⦄ = t-join
⋆-def ⦃ BinaryTreeMonad ⦄ (leaf x) v = Id.refl (fmap (x ,_) v)
⋆-def ⦃ BinaryTreeMonad ⦄ (l /\ r) v =
  ap2 _/\_ (⋆-def ⦃ BinaryTreeMonad ⦄ l v)
           (⋆-def ⦃ BinaryTreeMonad ⦄ r v)
associativity ⦃ BinaryTreeMonad ⦄ = subrel $ fun-ext go
  where go : t-join {X = X} ∘ map t-join ~ t-join ∘ t-join
        go (leaf t) = Het.refl (t-join t)
        go (l /\ r) = ap2 _/\_ (go l) (go r)
unit1 ⦃ BinaryTreeMonad ⦄ = subrel $ fun-ext go
  where go : {X : 𝒰 ˙} → t-join {X = X} ∘ fmap pure ~ id
        go (leaf x) = Het.refl (leaf x)
        go (l /\ r) = ap2 _/\_ (go l) (go r)
unit2 ⦃ BinaryTreeMonad ⦄ = subrel $ fun-ext go
  where go : {X : 𝒰 ˙} → t-join {X = X} ∘ pure ~ id
        go (leaf x) = Het.refl (leaf x)
        go (l /\ r) = ap2 _/\_ (go l) (go r)
mon-naturality ⦃ BinaryTreeMonad ⦄ f = subrel {sup = _==_} $ fun-ext go
  where go : t-join ∘ fmap (fmap f) ~ fmap f ∘ t-join
        go (leaf x) = Het.refl (fmap f x)
        go (l /\ r) = ap2 _/\_ (go l) (go r)

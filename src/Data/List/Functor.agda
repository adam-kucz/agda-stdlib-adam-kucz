{-# OPTIONS --exact-split --prop  #-}
module Data.List.Functor where

open import Data.List.Definition
open import Data.List.Collection
open import Data.List.Operation
open import Data.List.Monoid

open import Universes
open import Data.Collection.Definition
open import Data.Functor
open import Data.Applicative
open import Data.Monad
open import Operation.Binary
open import Structure.Monoid
open import Function
  renaming (_∘ₛ_ to _∘_; _$_ to _$'_)
  using (universe-of; uncurry; id; ==→~)
open import Proof

instance
  ListFunctor : Functor {U = universe-of}(λ X → List X)
  ListApplicative : Applicative {U = universe-of}(λ X → List X)
  ListMonad : Monad {U = universe-of}(λ X → List X)

open import Function using (_~_)
open import Axiom.FunctionExtensionality

private
  map : (f : X → Y)(l : List X) → List Y
  map f [] = []
  map f (h ∷ l) = f h ∷ map f l

fmap ⦃ ListFunctor ⦄ = map
fmap-id ⦃ ListFunctor ⦄ = fun-ext go
  where go : map id ~ id
        go [] = refl []
        go (h ∷ t) = ap (h ∷_) (go t)
fmap-∘ ⦃ ListFunctor ⦄ g f = fun-ext go
  where go : map (g ∘ f) ~ map g ∘ map f
        go [] = refl []
        go (h ∷ t) = ap (g (f h) ∷_) $ go t

∈fmap :
  {X : 𝒰 ˙}{Y : 𝒱 ˙}
  {x : X}{l : List X}
  (f : (x : X) → Y)
  (p : x ∈ l)
  → ------------------
  f x ∈ (f <$> l)
∈fmap f (x∈x∷ t) = x∈x∷ f <$> t
∈fmap f (x∈tail h p) = x∈tail (f h) (∈fmap f p)

open import Logic hiding (_,_)

∈fmap⁻¹ : 
  {X : 𝒰 ˙}{Y : 𝒱 ˙}
  {y : Y}
  (l : List X)
  (f : (x : X) → Y)
  (p : y ∈ (f <$> l))
  → ------------------
  ∃ λ (x : X) → f x == y ∧ x ∈ l
∈fmap⁻¹ (h ∷ l) f (x∈x∷ .(f <$> l)) = h ∃., (refl (f h) _∧_., x∈x∷ l)
∈fmap⁻¹ (h ∷ l) f (x∈tail .(f h) p) with ∈fmap⁻¹ l f p
∈fmap⁻¹ (h ∷ l) f (x∈tail .(f h) p) | x ∃., (fx==y _∧_., x∈l) =
  x ∃., (fx==y _∧_., x∈tail h x∈l)

fmap-++ : {X : 𝒰 ˙}{Y : 𝒱 ˙}
  (f : X → Y)(l l' : List X)
  → ---------------------------------------
  f <$> l ++ l' == (f <$> l) ++ (f <$> l')
fmap-++ f [] l' = refl (f <$> l')
fmap-++ f (h ∷ l) l' = ap (f h ∷_) (fmap-++ f l l')

open import Type.Sum
  renaming (_×_ to _x_)
  using (pr₁; pr₂; _,_; [_×_]; Σ-assoc)

private
  _L⋆_ : (u : List X)(v : List Y) → List (X x Y)

  _⋆[_] : {X : 𝒰 ˙}{Y : 𝒱 ˙}(u : List X)(v : Y)
    → --------------------------
    u L⋆ [ v ] == fmap (_, v) u

  ++-L⋆ : (u u' : List X)(v : List Y)
    → ----------------------------------------
    (u ++ u') L⋆ v == (u L⋆ v) ++ (u' L⋆ v)

[] L⋆ _ = []
(h ∷ u) L⋆ v = fmap (h ,_) v ++ (u L⋆ v)

[] ⋆[ _ ] = refl []
(h ∷ u) ⋆[ v ] = ap ((h , v) ∷_) $ u ⋆[ v ]

++-L⋆ [] u' v = refl (u' L⋆ v)
++-L⋆ (h ∷ u) u' v =
  proof map (h ,_) v ++ ((u ++ u') L⋆ v)
    === map (h ,_) v ++ ((u L⋆ v) ++ (u' L⋆ v))
      :by: ap (fmap (h ,_) v ++_) $ ++-L⋆ u u' v
    === map (h ,_) v ++ (u L⋆ v) ++ (u' L⋆ v)
      :by: assoc _ (u L⋆ v) (u' L⋆ v)
  qed

open import Type.Unit renaming (⋆ to <⋆>)
open import Proposition.Identity hiding (refl)

functor ⦃ ListApplicative ⦄ = ListFunctor
unit ⦃ ListApplicative ⦄ = [ <⋆> ]
_⋆_ ⦃ ListApplicative ⦄ = _L⋆_
fmap-def ⦃ ListApplicative ⦄ f x =
  proof fmap f x
    === fmap (uncurry _$'_ ∘ (f ,_)) x
      :by: ap (λ — → fmap — x) $ fun-ext (λ x₁ → refl (f x₁))
    === fmap (uncurry _$'_) (fmap (f ,_) x)
      :by: ==→~ (fmap-∘ (uncurry _$'_) (f ,_)) x
    === fmap (uncurry _$'_) (fmap (f ,_) x ++ [])
      :by: ap (fmap (uncurry _$'_)) $ sym $ right-unit (fmap (f ,_) x)
  qed
naturality ⦃ ListApplicative ⦄ f g [] v = refl []
naturality ⦃ ListApplicative ⦄ f g (u₀ ∷ u) v =
  proof [ f × g ] <$> fmap (u₀ ,_) v ++ (u ⋆ v)
    === fmap [ f × g ] (fmap (u₀ ,_) v) ++ fmap [ f × g ] (u ⋆ v)
      :by: fmap-++ [ f × g ] (fmap (u₀ ,_) v) (u ⋆ v)
    === fmap [ f × g ] (fmap (u₀ ,_) v) ++ (fmap f u ⋆ fmap g v)
      :by: ap (fmap [ f × g ] (fmap (u₀ ,_) v) ++_) $
           naturality f g u v
    === fmap (f u₀ ,_) (fmap g v) ++ (fmap f u ⋆ fmap g v)
      :by: ap (λ — → — v ++ (fmap f u ⋆ fmap g v)) (
        proof fmap [ f × g ] ∘ fmap (u₀ ,_)
          === fmap ([ f × g ] ∘ (u₀ ,_))
            :by: Id.sym $ fmap-∘ [ f × g ] (u₀ ,_)
          === fmap ((f u₀ ,_) ∘ g)
            :by: ap fmap $ fun-ext (λ v' → refl (f u₀ , g v'))
          === fmap (f u₀ ,_) ∘ fmap g
            :by: fmap-∘ (f u₀ ,_) g 
        qed)
  qed
left-identity ⦃ ListApplicative ⦄ v =
  proof fmap pr₂ (fmap (<⋆> ,_) v ++ [])
    === fmap pr₂ (fmap (<⋆> ,_) v)
      :by: ap (fmap pr₂) $ right-unit (fmap (<⋆> ,_) v)
    === fmap (pr₂ ∘ (<⋆> ,_)) v
      :by: ==→~ (sym $ fmap-∘ pr₂ (<⋆> ,_)) v
    === fmap id v
      :by: ap (λ — → fmap — v) $ fun-ext refl
    === v
      :by: ==→~ fmap-id v
  qed
right-identity ⦃ ListApplicative ⦄ u =
  proof fmap pr₁ (u ⋆ [ <⋆> ])
    === fmap pr₁ (fmap (_, <⋆>) u)
      :by: ap (fmap pr₁) (u ⋆[ <⋆> ])
    === fmap (pr₁ ∘ (_, <⋆>)) u
      :by: ==→~ (sym $ fmap-∘ pr₁ (_, <⋆>)) u
    === fmap id u
      :by: ap (λ — → fmap — u) $ fun-ext refl
    === u
      :by: ==→~ fmap-id u
  qed
⋆-assoc ⦃ ListApplicative ⦄ [] v w = refl []
⋆-assoc ⦃ ListApplicative ⦄ (h ∷ u) v w =
  proof fmap Σ-assoc (fmap (h ,_) (v ⋆ w) ++ (u ⋆ (v ⋆ w)))
    === fmap Σ-assoc (fmap (h ,_) (v ⋆ w)) ++ fmap Σ-assoc (u ⋆ (v ⋆ w))
      :by: fmap-++ Σ-assoc _ (u ⋆ (v ⋆ w))
    === fmap Σ-assoc (fmap (h ,_) (v ⋆ w)) ++ (u ⋆ v ⋆ w)
      :by: ap (fmap Σ-assoc (fmap (h ,_) (v ⋆ w)) ++_) $
           ⋆-assoc u v w
    === fmap (Σ-assoc ∘ (h ,_)) (v ⋆ w) ++ (u ⋆ v ⋆ w)
      :by: ap (λ — → — (v ⋆ w) ++ (u ⋆ v ⋆ w)) $
           Id.sym $ fmap-∘ Σ-assoc (h ,_)
    === (fmap (h ,_) v ⋆ w) ++ (u ⋆ v ⋆ w)
      :by: ap (_++ (u ⋆ v ⋆ w)) $ go v
    === (fmap (h ,_) v ++ (u ⋆ v)) ⋆ w
      :by: Id.sym $ ++-L⋆ (fmap (h ,_) v) (u ⋆ v) w 
  qed
  where go : {X : 𝒰 ˙}(v : List X)
          → --------------------------------------------------
          fmap (Σ-assoc ∘ (h ,_)) (v L⋆ w) == fmap (h ,_) v L⋆ w
        go [] = refl []
        go (v₀ ∷ v) =
          proof fmap (Σ-assoc ∘ (h ,_)) (fmap (v₀ ,_) w ++ (v L⋆ w))
            === fmap (Σ-assoc ∘ (h ,_)) (fmap (v₀ ,_) w) ++ fmap (Σ-assoc ∘ (h ,_)) (v L⋆ w)
              :by: fmap-++ (Σ-assoc ∘ (h ,_)) _ (v L⋆ w)
            === fmap (Σ-assoc ∘ (h ,_)) (fmap (v₀ ,_) w) ++ (fmap (h ,_) v L⋆ w)
              :by: ap (fmap (Σ-assoc ∘ (h ,_)) (fmap (v₀ ,_) w) ++_) $ go v
            === fmap (h , v₀ ,_) w ++ (fmap (h ,_) v L⋆ w)
              :by: ap (_++ (fmap (h ,_) v L⋆ w)) (
                proof fmap (Σ-assoc ∘ (h ,_)) (fmap (v₀ ,_) w)
                  === fmap (Σ-assoc ∘ (h ,_) ∘ (v₀ ,_)) w
                    :by: ==→~ (Id.sym $ fmap-∘ (Σ-assoc ∘ (h ,_)) (v₀ ,_)) w
                  === fmap (h , v₀ ,_) w
                    :by: ap (λ — → fmap — w) $ fun-ext (λ x → refl (h , v₀ , x))
                qed)
          qed

open import Proposition.Identity.Homogeneous using (het==→==)

applicative ⦃ ListMonad ⦄ = ListApplicative
join ⦃ ListMonad ⦄ = mconcat
⋆-def ⦃ ListMonad ⦄ [] v = refl []
⋆-def ⦃ ListMonad ⦄ (u₀ ∷ u) v = ap (fmap (u₀ ,_) v ++_) (⋆-def u v)
associativity ⦃ ListMonad ⦄ = fun-ext go
  where go : mconcat ∘ fmap mconcat ~ mconcat ∘ mconcat
        go [] = refl []
        go ([] ∷ t) = go t
        go (([] ∷ t₀) ∷ t₁) = go (t₀ ∷ t₁)
        go (((h ∷ t₀) ∷ t₁) ∷ t₂) = ap (h ∷_) (
          proof t₀ ++ mconcat t₁ ++ mconcat (mconcat <$> t₂)
            === t₀ ++ (mconcat t₁ ++ mconcat (mconcat <$> t₂))
              :by: sym $ assoc t₀ _ _
            === t₀ ++ mconcat (t₁ ++ mconcat t₂)
              :by: ap (t₀ ++_) (
                proof mconcat t₁ ++ mconcat (fmap mconcat t₂)
                  === mconcat t₁ ++ mconcat (mconcat t₂)
                    :by: ap (mconcat t₁ ++_) (go t₂)
                  === mconcat (t₁ ++ mconcat t₂)
                    :by: sym $ mconcat-++ t₁ (mconcat t₂)
                qed)
          qed)
unit1 ⦃ ListMonad ⦄ = het==→== $ fun-ext go
  where go : mconcat ∘ fmap pure ~ id
        go [] = refl []
        go (h ∷ t) = ap (h ∷_) (go t)
unit2 ⦃ ListMonad ⦄ = het==→== $ fun-ext go
  where go : mconcat ∘ pure ~ id
        go [] = refl []
        go (h ∷ t) = ap (h ∷_) (go t)

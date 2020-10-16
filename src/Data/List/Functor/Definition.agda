{-# OPTIONS --exact-split --prop  #-}
module Data.List.Functor.Definition where

open import Data.List.Definition
open import Data.List.Collection
open import Data.List.Operation
open import Data.List.Monoid

open import Universes
open import Collection.Definition
open import Data.Functor
open import Data.Applicative
open import Data.Monad
open import Operation.Binary
open import Structure.Monoid
open import Function
  renaming (_∘ₛ_ to _∘_; _$_ to _$'_)
  using (universe-of; uncurry; id; 𝑖𝑑; ==→~; _~_)
open import Proof

instance
  ListFunctor : Functor {U = universe-of}(λ X → List X)
  ListApplicative : Applicative {U = universe-of}(λ X → List X)
  ListMonad : Monad {U = universe-of}(λ X → List X)

open import Relation.Binary hiding (_~_)
open import Axiom.FunctionExtensionality

fmap ⦃ ListFunctor ⦄ = map
fmap-id ⦃ ListFunctor ⦄ = subrel $ fun-ext go
  where go : map (𝑖𝑑 X) ~ 𝑖𝑑 (List X)
        go [] = refl []
        go (h ∷ t) = ap (h ∷_) (go t)
fmap-∘ ⦃ ListFunctor ⦄ g f = subrel {_P_ = _==_} $ fun-ext $ map-∘ g f

fmap-L++ : {X : 𝒰 ˙}{Y : 𝒱 ˙}
  (f : X → Y)(l l' : List X)
  → ---------------------------------------
  f <$> l ++ l' == (f <$> l) ++ (f <$> l')
fmap-L++ f [] l' = refl (f <$> l')
fmap-L++ f (h ∷ l) l' = ap (f h ∷_) (fmap-L++ f l l')

open import Type.Sum
  renaming (_×_ to _x_; 〈_×_〉 to [_×_])
  using (pr₁; pr₂; _,_; Σ-assoc)

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
      :by: ap (λ — → fmap — x) $ subrel $ fun-ext (λ x₁ → refl (f x₁))
    === fmap (uncurry _$'_) (fmap (f ,_) x)
      :by: subrel $ ==→~ (fmap-∘ (uncurry _$'_) (f ,_)) x
    === fmap (uncurry _$'_) (fmap (f ,_) x ++ [])
      :by: ap (fmap (uncurry _$'_)) $ sym {R = _==_} $
           right-unit {e = []} (fmap (f ,_) x)
  qed
naturality ⦃ ListApplicative ⦄ f g [] v = refl []
naturality ⦃ ListApplicative ⦄ f g (u₀ ∷ u) v =
  proof [ f × g ] <$> fmap (u₀ ,_) v ++ (u ⋆ v)
    === fmap [ f × g ] (fmap (u₀ ,_) v) ++ fmap [ f × g ] (u ⋆ v)
      :by: fmap-L++ [ f × g ] (fmap (u₀ ,_) v) (u ⋆ v)
    === fmap [ f × g ] (fmap (u₀ ,_) v) ++ (fmap f u ⋆ fmap g v)
      :by: ap (fmap [ f × g ] (fmap (u₀ ,_) v) ++_) $
           naturality f g u v
    === fmap (f u₀ ,_) (fmap g v) ++ (fmap f u ⋆ fmap g v)
      :by: ap (λ — → — v ++ (fmap f u ⋆ fmap g v)){r = _==_}(
        proof fmap [ f × g ] ∘ fmap (u₀ ,_)
          === fmap ([ f × g ] ∘ (u₀ ,_))
            :by: sym {R = _==_} $ fmap-∘ [ f × g ] (u₀ ,_)
          === fmap ((f u₀ ,_) ∘ g)
            :by: ap fmap $
                 subrel {_P_ = _==_} $
                 fun-ext (λ v' → refl (f u₀ , g v'))
          === fmap (f u₀ ,_) ∘ fmap g
            :by: fmap-∘ (f u₀ ,_) g 
        qed)
  qed
left-identity ⦃ ListApplicative ⦄ v =
  proof fmap pr₂ (fmap (<⋆> ,_) v ++ [])
    === fmap pr₂ (fmap (<⋆> ,_) v)
      :by: ap (fmap pr₂) $ right-unit (fmap (<⋆> ,_) v)
    === fmap (pr₂ ∘ (<⋆> ,_)) v
      :by: subrel $ ==→~ (sym $ fmap-∘ pr₂ (<⋆> ,_)) v
    === fmap id v
      :by: ap (λ — → fmap — v) $ subrel $ fun-ext refl
    === v
      :by: subrel $ ==→~ fmap-id v
  qed
right-identity ⦃ ListApplicative ⦄ u =
  proof fmap pr₁ (u ⋆ [ <⋆> ])
    === fmap pr₁ (fmap (_, <⋆>) u)
      :by: ap (fmap pr₁) (u ⋆[ <⋆> ])
    === fmap (pr₁ ∘ (_, <⋆>)) u
      :by: subrel $ ==→~ (sym $ fmap-∘ pr₁ (_, <⋆>)) u
    === fmap id u
      :by: ap (λ — → fmap — u) $ subrel $ fun-ext refl
    === u
      :by: subrel $ ==→~ fmap-id u
  qed
⋆-assoc ⦃ ListApplicative ⦄ [] v w = refl []
⋆-assoc ⦃ ListApplicative ⦄ (h ∷ u) v w =
  proof fmap Σ-assoc (fmap (h ,_) (v ⋆ w) ++ (u ⋆ (v ⋆ w)))
    === fmap Σ-assoc (fmap (h ,_) (v ⋆ w)) ++ fmap Σ-assoc (u ⋆ (v ⋆ w))
      :by: fmap-L++ Σ-assoc _ (u ⋆ (v ⋆ w))
    === fmap Σ-assoc (fmap (h ,_) (v ⋆ w)) ++ (u ⋆ v ⋆ w)
      :by: ap (fmap Σ-assoc (fmap (h ,_) (v ⋆ w)) ++_) $
           ⋆-assoc u v w
    === fmap (Σ-assoc ∘ (h ,_)) (v ⋆ w) ++ (u ⋆ v ⋆ w)
      :by: ap (λ — → — (v ⋆ w) ++ (u ⋆ v ⋆ w)) $
           sym {R = _==_} $
           fmap-∘ Σ-assoc (h ,_)
    === (fmap (h ,_) v ⋆ w) ++ (u ⋆ v ⋆ w)
      :by: ap (_++ (u ⋆ v ⋆ w)) $ go v
    === (fmap (h ,_) v ++ (u ⋆ v)) ⋆ w
      :by: sym {R = _==_} $ ++-L⋆ (fmap (h ,_) v) (u ⋆ v) w 
  qed
  where go : {X : 𝒰 ˙}(v : List X)
          → --------------------------------------------------
          fmap (Σ-assoc ∘ (h ,_)) (v L⋆ w) == fmap (h ,_) v L⋆ w
        go [] = refl []
        go (v₀ ∷ v) =
          proof fmap (Σ-assoc ∘ (h ,_)) (fmap (v₀ ,_) w ++ (v L⋆ w))
            === fmap (Σ-assoc ∘ (h ,_)) (fmap (v₀ ,_) w) ++ fmap (Σ-assoc ∘ (h ,_)) (v L⋆ w)
              :by: fmap-L++ (Σ-assoc ∘ (h ,_)) _ (v L⋆ w)
            === fmap (Σ-assoc ∘ (h ,_)) (fmap (v₀ ,_) w) ++ (fmap (h ,_) v L⋆ w)
              :by: ap (fmap (Σ-assoc ∘ (h ,_)) (fmap (v₀ ,_) w) ++_) $ go v
            === fmap (h , v₀ ,_) w ++ (fmap (h ,_) v L⋆ w)
              :by: ap (_++ (fmap (h ,_) v L⋆ w)){r = _==_}(
                proof fmap (Σ-assoc ∘ (h ,_)) (fmap (v₀ ,_) w)
                  === fmap (Σ-assoc ∘ (h ,_) ∘ (v₀ ,_)) w
                    :by: subrel {_P_ = _==_} $
                         ==→~ (sym {R = _==_} $ fmap-∘ (Σ-assoc ∘ (h ,_)) (v₀ ,_)) w
                  === fmap (h , v₀ ,_) w
                    :by: ap (λ — → fmap — w) $
                         subrel {_P_ = _==_} $
                         fun-ext (λ x → refl (h , v₀ , x))
                qed)
          qed

open import Proposition.Identity.Homogeneous

applicative ⦃ ListMonad ⦄ = ListApplicative
join ⦃ ListMonad ⦄ = mconcat
⋆-def ⦃ ListMonad ⦄ [] v = Id.refl []
⋆-def ⦃ ListMonad ⦄ (u₀ ∷ u) v = ap (fmap (u₀ ,_) v ++_) (⋆-def u v)
associativity ⦃ ListMonad ⦄ = subrel $ fun-ext go
  where go : mconcat ∘ fmap mconcat ~ mconcat ∘ mconcat
        go [] = Het.refl []
        go ([] ∷ t) = go t
        go (([] ∷ t₀) ∷ t₁) = go (t₀ ∷ t₁)
        go (((h ∷ t₀) ∷ t₁) ∷ t₂) = subrel $ ap (h ∷_){r = _==_}(
          proof t₀ ++ mconcat t₁ ++ mconcat (mconcat <$> t₂)
            === t₀ ++ (mconcat t₁ ++ mconcat (mconcat <$> t₂))
              :by: sym $ assoc t₀ _ _
            === t₀ ++ mconcat (t₁ ++ mconcat t₂)
              :by: ap (t₀ ++_){r = _==_}(
                proof mconcat t₁ ++ mconcat (fmap mconcat t₂)
                  === mconcat t₁ ++ mconcat (mconcat t₂)
                    :by: ap (mconcat t₁ ++_) (subrel $ go t₂)
                  === mconcat (t₁ ++ mconcat t₂)
                    :by: sym $ mconcat-∪ t₁ (mconcat t₂)
                qed)
          qed)
unit1 ⦃ ListMonad ⦄ = subrel $ fun-ext go
  where go : mconcat ∘ fmap pure ~ id
        go [] = Het.refl []
        go (h ∷ t) = ap (h ∷_) (go t)
unit2 ⦃ ListMonad ⦄ = subrel $ fun-ext go
  where go : mconcat ∘ pure ~ id
        go [] = Het.refl []
        go (h ∷ t) = ap (h ∷_) (go t)
mon-naturality ⦃ ListMonad ⦄ f = subrel {_P_ = _==_} $ fun-ext go
  where go : mconcat ∘ fmap (fmap f) ~ fmap f ∘ mconcat
        go [] = Het.refl []
        go ([] ∷ t) = go t
        go ((h ∷ t₀) ∷ t₁) = ap (f h ∷_) $ go (t₀ ∷ t₁)

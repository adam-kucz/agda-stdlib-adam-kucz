{-# OPTIONS --safe --exact-split --prop  #-}
open import PropUniverses

module Data.List.Operation {𝒰 : Universe} where

open import Data.List.Definition
open import Data.List.Property
open import Data.List.Collection
open import Data.List.Insertable

open import Proposition.Identity
open import Proposition.Decidable
open import Data.Nat
open import Data.Maybe
open import Data.Functor
open import Data.Collection hiding (_++_)
open import Logic

_++_ : (l l' : List X) → List X
[] ++ l' = l'
(h ∷ l) ++ l' = h ∷ (l ++ l')

open import Operation.Binary

instance
  ++-assoc : Associative (_++_ {X = X})
  assoc ⦃ ++-assoc ⦄ [] y z = refl (y ++ z)
  assoc ⦃ ++-assoc ⦄ (h ∷ x) y z =
    List== (refl h) (assoc x y z)

  []-++ : [] IsLeftUnitOf (_++_ {X = X})
  left-unit ⦃ []-++ ⦄ = refl

  ++-[] : [] IsRightUnitOf (_++_ {X = X})
  right-unit ⦃ ++-[] ⦄ [] = refl []
  right-unit ⦃ ++-[] ⦄ (h ∷ t) =
    List== (refl h) (right-unit t)

open import Structure.Monoid

ListMonoid : Monoid (List X)
_∙_ ⦃ ListMonoid ⦄ = _++_
e ⦃ ListMonoid ⦄ = []

filter :
  (p : X → 𝒰 ᵖ)
  ⦃ _ : ∀ {x} → Decidable (p x) ⦄
  (l : List X)
  → --------------------
  List X
filter _ [] = []
filter p (h ∷ _) with decide (p h)
filter p (h ∷ l) | true _ = h ∷ filter p l
filter p (_ ∷ l) | false _ = filter p l

∈filter : 
  (p : X → 𝒰 ᵖ)
  ⦃ d : ∀ {x} → Decidable (p x) ⦄
  (l : List X)
  (x : X)
  → --------------------
  x ∈ filter p l ↔ x ∈ l ∧ p x
⟶ (∈filter p [] x) ()
⟵ (∈filter p [] x) ()
∈filter p ⦃ d ⦄ (h ∷ l) x with decide (p h) ⦃ d ⦄
∈filter p (h ∷ l) x | true q = (
  λ { (x∈x∷ .(filter p l)) → x∈x∷ l , q
    ; (x∈tail h p₁) → let ih = ⟶ (∈filter p l x) p₁ in
         x∈tail h (∧left ih) , ∧right ih}) ,
  λ { (x∈x∷ t , _) → x∈x∷ filter p l 
    ; (x∈tail h x∈l , px) → x∈tail h (⟵ (∈filter p l x) (x∈l , px)) }
∈filter p (h ∷ l) x | false ¬q =
  (λ p₁ → let ih = ⟶ (∈filter p l x) p₁ in
     x∈tail h (∧left ih) , ∧right ih) ,
  λ { (x∈x∷ _ , ph) → ⊥-recursion (h ∈ filter p l) (¬q ph)
    ; (x∈tail _ x∈l , px) → ⟵ (∈filter p l x) (x∈l , px) }

module WithDecidableElement==
  {X : 𝒰 ˙}
  ⦃ d : {x y : X} → Decidable (x == y) ⦄
  where
  
  find : (x : X) (l : List X) → Maybe ℕ
  find x [] = nothing
  find x (h ∷ l) with decide (x == h)
  find x (h ∷ l) | true  _ = just 0
  find x (h ∷ l) | false _ = fmap suc (find x l)
  
  index : {x : X} {l : List X} (p : x ∈ l) → ℕ
  index {x = x} {h ∷ l} p with decide (x == h)
  index {x = x} {h ∷ l} p | true   x==h = 0
  index {x = x} {h ∷ l} p | false ¬x==h = suc (index (prev p))
    where open import Proposition.Empty
          prev : (p : x ∈ h ∷ l) → x ∈ l
          prev (x∈x∷ t) = ⊥-recursionₚ (x ∈ l) (¬x==h (refl x))
          prev (x∈tail _ p) = p
  
  multiplicity : (x : X) (l : List X) → ℕ
  multiplicity x [] = 0
  multiplicity x (h ∷ l) with decide (x == h)
  multiplicity x (h ∷ l) | true  _ = suc (multiplicity x l)
  multiplicity x (h ∷ l) | false _ = multiplicity x l

open WithDecidableElement== public



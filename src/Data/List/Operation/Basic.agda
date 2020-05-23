{-# OPTIONS --safe --exact-split --prop  #-}
module Data.List.Operation.Basic where

open import Data.List.Definition
open import Data.List.Collection
open import Data.List.Insertable

open import PropUniverses
open import Proposition.Identity hiding (refl)
open import Proposition.Empty
open import Proposition.Decidable.Definition
open import Data.Nat.Definition
open import Data.Maybe.Definition
open import Data.Functor
open import Collection.Definition
open import Logic hiding (⊥-recursion)
open import Proof

head : (l : List X)(p : l ≠ [] {X = X}) → X
head {X = X} [] p = ⊥-recursion X (p (refl []))
head (h ∷ _) p = h

tail : (l : List X)(p : l ≠ [] {X = X}) → List X
tail {X = X} [] p = ⊥-recursion (List X) (p (refl []))
tail (_ ∷ t) p = t

infixl 105 _++_
_++_ : (l l' : List X) → List X
[] ++ l' = l'
(h ∷ l) ++ l' = h ∷ (l ++ l')

open import Operation.Binary

instance
  ++-assoc : Associative (_++_ {X = X})
  []-++ : [] IsLeftUnitOf (_++_ {X = X})
  ++-[] : [] IsRightUnitOf (_++_ {X = X})
  
assoc ⦃ ++-assoc ⦄ [] y z = refl (y ++ z)
assoc ⦃ ++-assoc ⦄ (h ∷ x) y z =
  List== (refl h) (assoc x y z)

left-unit ⦃ []-++ ⦄ = refl

right-unit ⦃ ++-[] ⦄ [] = refl []
right-unit ⦃ ++-[] ⦄ (h ∷ t) =
  List== (refl h) (right-unit t)

∈++ : {x : X}
  (l l' : List X)
  → ----------------------------
  x ∈ l ++ l' ↔ x ∈ l ∨ x ∈ l'
⟶ (∈++ [] l') p = ∨right p
⟵ (∈++ [] l') (∨right q) = q
⟶ (∈++ (h ∷ l) l') (x∈x∷ .(l ++ l')) = ∨left $ x∈x∷ l
⟶ (∈++ (h ∷ l) l') (x∈tail h p) with ⟶ (∈++ l l') p
⟶ (∈++ (h ∷ l) l') (x∈tail h p) | ∨left q = ∨left $ x∈tail h q
⟶ (∈++ (h ∷ l) l') (x∈tail h p) | ∨right q = ∨right q
⟵ (∈++ (h ∷ l) l') (∨left (x∈x∷ l)) = x∈x∷ l ++ l'
⟵ (∈++ (h ∷ l) l') (∨left (x∈tail h p)) = x∈tail h $ ⟵ (∈++ l l') $ ∨left p
⟵ (∈++ (h ∷ l) l') (∨right q) = x∈tail h $ ⟵ (∈++ l l') $ ∨right q

open import Data.Nat.Arithmetic.Definition

map : (f : X → Y)(l : List X) → List Y
map f [] = []
map f (h ∷ l) = f h ∷ map f l

filter :
  (p : X → 𝒰 ᵖ)
  ⦃ d : ∀ {x} → Decidable (p x) ⦄
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
  λ { (x∈x∷ _ , ph) → ⊥-recursionₚ (h ∈ filter p l) (¬q ph)
    ; (x∈tail _ x∈l , px) → ⟵ (∈filter p l x) (x∈l , px) }

drop-last : (l : List X)(p : l ≠ [] {X = X}) → List X
drop-last {X = X} [] p = ⊥-recursion (List X) (p (refl [])) 
drop-last [ h ] p = []
drop-last (h₀ ∷ h₁ ∷ t) p = h₀ ∷ drop-last (h₁ ∷ t) λ ()

drop-last++last== : ∀ l
  (p : l ≠ [] {X = X})
  → -----------------------------------
  drop-last l p ++ [ last l p ] == l
drop-last++last==  [] p = ⊥-recursionₚ _ (p (refl [])) 
drop-last++last== [ h ] p = refl [ h ]
drop-last++last== (h₀ ∷ h₁ ∷ t) p =
  List== (refl h₀) (drop-last++last== (h₁ ∷ t) λ ())


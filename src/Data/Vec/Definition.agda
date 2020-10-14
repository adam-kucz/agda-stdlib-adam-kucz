{-# OPTIONS --safe --exact-split  #-}
module Data.Vec.Definition where

open import Universes
open import Data.Nat

infixr 115 _∷_
data Vec (X : 𝒰 ˙) : (n : ℕ) → 𝒰 ˙ where
  []  : Vec X 0
  _∷_ : ∀ {n} (h : X) (t : Vec X n) → Vec X (suc n)

open import Data.Nat

head : ∀ {m}(v : Vec X (m +1)) → X
head (h ∷ _) = h

tail : ∀ {m}(v : Vec X (m +1)) → Vec X m
tail (_ ∷ t) = t

open import Proof
open import Data.Maybe

infixr 110 _!_
_!_ : (l : Vec X m) → [ n ∶ ℕ ]⇀ X
[] ! _ = nothing
h ∷ _ ! zero = just h
_ ∷ l ! n +1 = l ! n

pattern [_] a₀ = a₀ ∷ []
pattern [_⸴_] a₀ a₁ = a₀ ∷ a₁ ∷ []
pattern [_⸴_⸴_] a₀ a₁ a₂ = a₀ ∷ a₁ ∷ a₂ ∷ []
pattern [_⸴_⸴_⸴_] a₀ a₁ a₂ a₃ = a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ []

open import Logic

Vec== : ∀ {m}
  {h1 h2 : X} {t1 t2 : Vec X m}
  → -----------------------------------------
  h1 ∷ t1 == h2 ∷ t2 ↔ h1 == h2 ∧ t1 == t2
⟶ Vec== (Id.refl (h ∷ t)) = refl h , refl t
⟵ Vec== (Id.refl h , Id.refl t) = refl (h ∷ t)

last : {m : ℕ}(v : Vec X (m +1)) → X
last [ h ] = h
last (_ ∷ h₁ ∷ v) = last (h₁ ∷ v)

drop-last : (v : Vec X (m +1)) → Vec X m
drop-last [ _ ] = []
drop-last (h₀ ∷ h₁ ∷ v) = h₀ ∷ drop-last (h₁ ∷ v)

-- delete-nth : (k : ℕ)(p : k ≤ m)(v : Vec X (m +1)) → Vec X m
-- delete-nth zero p (h ∷ v) = v
-- delete-nth {m +1} (k +1) p (h ∷ v) = h ∷ delete-nth k (ap pred p) v

infixl 105 _++_
_++_ : ∀ {m n}(v : Vec X m)(v' : Vec X n) → Vec X (m + n)
[] ++ v' = v'
h ∷ v ++ v' = h ∷ (v ++ v')

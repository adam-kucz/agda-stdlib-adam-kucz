{-# OPTIONS --safe --exact-split --prop  #-}
module Data.Vec.Function where

open import Data.Vec.Definition
open import Data.Vec.Property

open import Universes
open import Data.List as L
  hiding ([_]; map; _++_; ∈++; last;
          drop-last; reverse; zip; ∈map; ∈map⁻¹)
open import Collection hiding (_~_; _++_)

map : ∀ {n}(f : X → Y)(v : Vec X n) → Vec Y n
map _ [] = []
map f (h ∷ v) = f h ∷ map f v

dmap : ∀ {n}(v : Vec X n)(f : (x : X)(p : x ∈ v) → Y) → Vec Y n
dmap [] _ = []
dmap (h ∷ v) f = f h (x∈x∷ v) ∷ dmap v λ x p → f x (x∈tail h p)

open import Logic
open import Proof

∈map : ∀{n}
  {x : X}{v : Vec X n}
  (f : (x : X) → Y)
  (p : x ∈ v)
  → ------------------
  f x ∈ map f v
∈map f (x∈x∷ t) = x∈x∷ (map f t)
∈map f (x∈tail h p) = x∈tail (f h) $ ∈map f p

∈map⁻¹ : ∀{n}
  {y : Y}
  (v : Vec X n)
  (f : (x : X) → Y)
  (p : y ∈ map f v)
  → ------------------
  ∃ λ (x : X) → f x == y ∧ x ∈ v
∈map⁻¹ (h ∷ v) f (x∈x∷ .(map f v)) = h , (Id.refl _ , x∈x∷ v)
∈map⁻¹ (h ∷ v) f (x∈tail .(f h) p) with ∈map⁻¹ v f p
∈map⁻¹ (h ∷ v) f (x∈tail .(f h) p) | x , (Id.refl _ , x∈v) =
  x , (Id.refl _ , x∈tail h x∈v)

map-as-dmap : ∀ {n}
  (f : X → Y)
  (v : Vec X n)
  → -----------------------------------------
  map f v == dmap v λ x _ → f x
map-as-dmap f [] = Id.refl []
map-as-dmap f (h ∷ v) = ap (f h ∷_) $ map-as-dmap f v

∈dmap : ∀{X : 𝒰 ˙}{n}
  {x : X}{v : Vec X n}
  (f : (x : X)(p : x ∈ v) → Y)
  (p : x ∈ v)
  → ------------------
  f x p ∈ dmap v f
∈dmap {v = h ∷ v} f (x∈x∷ v) = x∈x∷ dmap v λ x p → f x (x∈tail h p)
∈dmap {v = h ∷ v} f (x∈tail h p) =
  x∈tail (f h (x∈x∷ v)) (∈dmap (λ x p → f x (x∈tail h p)) p)

dmap-id : ∀{m}
  (v : Vec X m)
  → ------------------------------
  dmap v (λ x _ → x) == v
dmap-id [] = Id.refl []
dmap-id (h ∷ v) = ap (h ∷_) $ dmap-id v

dmap-∘ : ∀{X : 𝒰 ˙}{Y : 𝒱 ˙}{n}
  (v : Vec X n)
  (f : (x : X)(p : x ∈ v) → Y)
  (g : (y : Y)(p : y ∈ dmap v f) → Z)
  → -------------------------------------
  dmap (dmap v f) g == dmap v λ x p → g (f x p) (∈dmap f p)
dmap-∘ [] f g = Id.refl []
dmap-∘ (h ∷ v) f g =
  ap (g (f h (x∈x∷ v)) (x∈x∷ _) ∷_) $
  dmap-∘ v (λ x p → f x (x∈tail _ p)) (λ y p → g y (x∈tail _ p))

dmap++ : ∀{X : 𝒰 ˙}{m n}
  (v₀ : Vec X m)
  (v₁ : Vec X n)
  (f : (x : X)(p : x ∈ v₀ ++ v₁) → Y)
  → ------------------------------
  dmap v₀ (λ x p → f x (⟵ (∈++ v₀ v₁) $ ∨left p)) ++
  dmap v₁ (λ x p → f x (⟵ (∈++ v₀ v₁) $ ∨right p))
  ==
  dmap (v₀ ++ v₁) f
dmap++ [] [] f = Id.refl []
dmap++ [] (h ∷ v₁) f = ap (f h _ ∷_) $ dmap++ [] v₁ λ x p → f x (x∈tail h p)
dmap++ (h ∷ v₀) v₁ f = ap (f h _ ∷_) $ dmap++ v₀ v₁ λ x p → f x (x∈tail h p)

to-vec : (l : List X) → Vec X (len l)
to-vec [] = []
to-vec (h ∷ l) = h ∷ to-vec l

open import Data.NonemptyList as NL hiding ([_])

nonempty-to-vec : (l : NonemptyList X) → Vec X (len l)
nonempty-to-vec NL.[ x ] = [ x ]
nonempty-to-vec (h ∷ l) = h ∷ nonempty-to-vec l

open import Data.Nat

vec-to-nonempty-list : (v : Vec X (m +1)) → NonemptyList X
vec-to-nonempty-list [ h ] = NL.[ h ]
vec-to-nonempty-list (h ∷ h₁ ∷ v) = h ∷ vec-to-nonempty-list (h₁ ∷ v)

-- open import Proposition.Identity hiding (refl)
open import Proposition.Empty renaming (⊥-recursion to ⊥ₜ-recursion)
open import Proposition.Decidable
open import Relation.Binary hiding (_~_)
open import Proof

vec-remove :
  (x : X)
  (v : Vec X (m +1))
  (p : x ∈ v)
  ⦃ dec== : HasDecidableIdentity X ⦄
  → --------------------
  Vec X m
vec-remove x (h ∷ v) p with decide (h == x)
vec-remove x (h ∷ v) p | true _ = v
vec-remove {m = zero} x [ h ] p | false ¬p =
  ⊥ₜ-recursion (Vec _ 0) (contradiction p)
  where contradiction : (p : x ∈ [ h ]) → ⊥
        contradiction (x∈x∷ t) = ¬p $ Id.refl x
vec-remove {m = m +1} x (h ∷ v) p | false ¬p =
  h ∷ vec-remove x v (p' p)
  where p' : (p : x ∈ h ∷ v) → x ∈ v
        p' (x∈x∷ t) = ⊥-recursionₚ (x ∈ v) $ ¬p $ Id.refl x
        p' (x∈tail h p) = p

open import Function hiding (_$_)

to-vec-to-list : to-vec ∘ (to-list {Col = Vec X m}) ~ id
to-vec-to-list [] = refl []
to-vec-to-list {X = X} (h ∷ v) =
  Het.Id.ap2 {K = λ m v → Vec X (m +1)}
             (λ m (v : Vec X m) → h ∷ v)
             (subrel $ vec-to-list-len v)
             (to-vec-to-list v)

to-list-to-vec : to-list ∘ (to-vec {X = X}) ~ id
to-list-to-vec [] = refl []
to-list-to-vec (h ∷ t) = ap (h ∷_) $ to-list-to-vec t

reverse : (v : Vec X m) → Vec X m
reverse [] = []
reverse v@(_ ∷ _) = last v ∷ reverse (drop-last v)

open import Type.Sum renaming (_,_ to _Σ,_)

zip : (v₀ : Vec X m)(v₁ : Vec Y m) → Vec (X × Y) m
zip [] [] = []
zip (h₀ ∷ v₀) (h₁ ∷ v₁) = (h₀ Σ, h₁) ∷ zip v₀ v₁

{-# OPTIONS --exact-split --prop #-}
module Type.Subset.Decidable where

open import Type.Subset.Definition as Def using (Subset)
import Type.Subset.Operation as Op

open import PropUniverses
open import Proposition.Decidable
open import Data.Collection

record DecSubset 𝒰 (X : 𝒱 ˙) : 𝒱 ⊔ 𝒰 ⁺ ˙ where
  constructor dec-set
  field
    set : Subset 𝒰 X
    ⦃ dec ⦄ : ∀ {x : X} → Decidable (x ∈ set)

instance
  DecSubsetCollection : Collection 𝒰 (DecSubset 𝒰 X) X

_∈_ ⦃ DecSubsetCollection ⦄ x (dec-set c) = c x

Decidable∈DecSubset : {x : X}{S : DecSubset 𝒰 X} → Decidable (x ∈ S)
Decidable∈DecSubset {x = x}{S} = decide (x ∈ S) ⦃ DecSubset.dec S ⦄

open import Logic

infixl 105 _∪_
_∪_ :
  (S₀ : DecSubset 𝒰 X)
  (S₁ : DecSubset 𝒱 X)
  → ------------------
  DecSubset (𝒰 ⊔ 𝒱) X
dec-set set₀ ∪ dec-set set₁ = dec-set (λ x → x ∈ set₀ ∨ x ∈ set₁)

open import Type.Sum hiding (_,_)
open import Proposition.Identity hiding (refl)
open import Proposition.Sum.Monoid
open import Proposition.Sum.Property
open import Proposition.Decidable.Monoid
open import Data.Collection.Listable.Function
open import Data.Functor
open import Data.List
open import Data.List.Functor
open import Structure.Monoid
open import Operation.Binary hiding (Inverse)
open import Function hiding (_$_)
open import Proof
open import Proposition.Proof

open import Axiom.PropositionExtensionality

infixr 105 _[_,_]`_
_[_,_]`_ : {X : 𝒰 ˙}{Y : 𝒱 ˙}
  (f : X → Y)
  (f⁻¹ : Y → List X)
  (p : ∀ x y → x ∈ f⁻¹ y ↔ f x == y)
  (S : DecSubset 𝒲 X)
  → ----------------
  DecSubset (𝒰 ⊔ 𝒱 ⊔ 𝒲) Y
_[_,_]`_ {𝒲 = 𝒲}{X = X}{Y} f f⁻¹ p S@(dec-set set) = dec-set (f Op.` set)
  where instance
          d : {y : Y} → Decidable (y ∈ f Op.` set)
          mon = Monoid∨
        func = λ x → (x ∈ set) Σ., DecSubset.dec S
        ls : (y : Y) → List (Σ λ (𝑋 : 𝒲 ᵖ) → Decidable 𝑋)
        ls y = func <$> (f⁻¹ y)
        d {y} with decide (fold-map pr₁ (ls y)) ⦃ decidable-fold (ls y) ⦄
        d {y} | true p' = true go
          where go : ∃ (λ x → f x == y ∧ set x)
                go with mconcat∨→elem (pr₁ <$> ls y) p'
                go | 𝑋 , (p , 𝑋∈) with have3
                  where have1 : fmap pr₁ ∘ fmap func == fmap (pr₁ ∘ func)
                        have1 = strong-sym $ fmap-∘ pr₁ func
                        have2 : 𝑋 ∈ fmap (_∈ set) (f⁻¹ y)
                        have2 = Id.coe (ap (λ — → 𝑋 ∈ — (f⁻¹ y)) have1) 𝑋∈
                        have3 : ∃ λ (x : X) → x ∈ set == 𝑋 ∧ x ∈ f⁻¹ y
                        have3 = ∈fmap⁻¹ (f⁻¹ y) (_∈ set) have2
                go | _ , (q , _) | x , (x∈set==𝑋 , x∈f⁻¹y) =
                  x , (⟶ (p x y) x∈f⁻¹y , ⟵ (==→↔ x∈set==𝑋) q)
        d {y} | false ∀x∉set = false go
          where go : ∃ (λ x → f x == y ∧ set x) → ⊥
                go (x' , (fx'==y , x'∈set)) =
                  have x' ∈ f⁻¹ y :from: ⟵ (p x' y) fx'==y
                    ⟶ ((x' ∈ set) Σ., DecSubset.dec S) ∈ ls y
                      :by: ∈fmap (λ x → (x ∈ set) Σ., DecSubset.dec S)
                    ⟶ (x' ∈ set) ∈ fmap pr₁ (ls y)
                      :by: ∈fmap pr₁
                    ⟶ Lift𝒰ᵖ ⊤ ∈ fmap pr₁ (ls y)
                      :by: ⟶ $ ==→↔ $ ap (_∈ fmap pr₁ (ls y)) $ ==Lift⊤ x'∈set
                    ⟶ mconcat (fmap pr₁ (ls y)) == Lift𝒰ᵖ ⊤
                      :by: mconcat-zero
                    ⟶ ¬ Lift𝒰ᵖ ⊤
                      :by: (λ q → ⟶ (==→↔ $ ap ¬_ q) ∀x∉set)
                    ⟶ ⊥
                      :by: (_$ (↑prop ⋆ₚ))

infixr 105 _`_
_`_ : {X : 𝒰 ˙}{Y : 𝒱 ˙}
  (f : X → Y)
  {f⁻¹ : Y → X}
  ⦃ inv : Inverse f f⁻¹ ⦄
  (S : DecSubset 𝒲 X)
  → ----------------
  DecSubset (𝒰 ⊔ 𝒱 ⊔ 𝒲) Y
_`_ f {f⁻¹} ⦃ inv ⦄ S = f [ [_] ∘ f⁻¹ , p ]` S
  where p : ∀ x y → x ∈ [ f⁻¹ y ] ↔ f x == y
        ⟶ (p .(f⁻¹ y) y) (x∈x∷ []) = right-inv y
        ⟵ (p x .(f x)) (Id.refl .(f x)) =
          Id.coe (ap (λ — → x ∈ [ — ]) $ sym $ left-inv x) $ x∈x∷ []

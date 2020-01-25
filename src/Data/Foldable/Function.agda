{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Data.Foldable.Definition

module Data.Foldable.Function
  {F : 𝒳 ˙ → 𝒵 ˙}
  ⦃ _ : Foldable F ⦄
  where

open import Function.Structure

open import Data.List.Definition
open import Data.List.Monoid

to-list : (fx : F X) → List X
to-list = fold-map ⦃ mon = ListMonoid ⦄ [_]

foldr :
  (f : X → Y → Y)
  (z : Y)
  → --------------------
  (fx : F X) → Y
foldr f z fx = fold-map ⦃ mon = EndoMonoid ⦄ f fx z

open import Function using (flip)
open import Structure.Monoid using (dual)

foldl :
  (f : Y → X → Y)
  (z : Y)
  → --------------------
  (fx : F X) → Y
foldl f z fx = fold-map ⦃ mon = dual EndoMonoid ⦄ (flip f) fx z

open import Proposition.Decidable
open import Structure.Monoid
open import Operation.Binary
open import Relation.Binary
open import Logic
open import Proof

-- best :
--   (_≤_ : Rel 𝒰 X X)
--   ⦃ d : ∀ {x y} → Decidable (x ≤ y) ⦄
--   (min : X)
--   ⦃ p₀ : Minimal _≤_ min ⦄
--   ⦃ p₁ : Connex _≤_ ⦄
--   (fx : F X) → X
-- best {X = X} _≤_ min = fold ⦃ m = BestMonoid ⦄
--   where gt : (x y : X) → X
--         gt x y = if x ≤ y then y else x
--         instance
--           r-unit : min IsRightUnitOf gt
--           right-unit ⦃ r-unit ⦄ y = (_== y) by-difₚ y ≤ min
--             then (λ p₁ → sym $ minimality p₁)
--             else λ ¬p → refl y
--           l-unit : min IsLeftUnitOf gt
--           left-unit ⦃ l-unit ⦄ y = (_== y) by-difₚ min ≤ y
--             then (λ p₁ → refl y)
--             else go
--             where go : (¬p : ¬ (min ≤ y)) → min == y
--                   go ¬p with total min y
--                   go ¬p | ∨left p = ⊥-recursion (min == y) (¬p p)
--                   go ¬p | ∨right q = sym $ minimality q
--           gt-assoc : Associative gt
--           assoc ⦃ gt-assoc ⦄ x y z = (λ — → gt x (gt y z) == gt — z) by-difₚ x ≤ y
--             then (λ p → (gt x (gt y z) ==_) by-difₚ y ≤ z
--               then {!!}
--               else {!!})
--             else λ ¬p → {!!}
--         BestMonoid : Monoid X
--         _∙_ ⦃ BestMonoid ⦄ = gt
--         e ⦃ BestMonoid ⦄ = min


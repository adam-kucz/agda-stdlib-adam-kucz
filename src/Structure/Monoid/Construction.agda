{-# OPTIONS --exact-split --safe #-}
module Structure.Monoid.Construction where

open import Structure.Monoid.Definition

open import Universes
open import Type.Identity
open import Function
open import Operation.Binary

instance
  IdRightUnit : 𝑖𝑑 X IsRightUnitOf (_∘ₛ_ {Z = Z})
  IdLeftUnit : 𝑖𝑑 Y IsLeftUnitOf (_∘ₛ_ {X = X})
  Associative-∘ : Associative (_∘ₛ_ {X = X})

right-unit ⦃ IdRightUnit ⦄ = refl
left-unit ⦃ IdLeftUnit ⦄ = refl
assoc ⦃ Associative-∘ ⦄ _ _ _ = refl _

EndofunctionMonoid : {X : 𝒰 ˙} → Monoid (X → X)
_∙_ ⦃ EndofunctionMonoid ⦄ = _∘ₛ_
e ⦃ EndofunctionMonoid ⦄ = id

-- JoinSemilatticeMonoid :
--   (lattice : JoinSemilattice 𝒰 X)
--   → let instance _ = lattice in
--   ⦃ d : ∀ {x y : X} → Decidable (x ⊑ y) ⦄
--   → -----------------------------------
--   Monoid X
-- _∙_ ⦃ JoinSemilatticeMonoid lattice ⦄ =  ?
-- e ⦃ JoinSemilatticeMonoid lattice ⦄ = {!!}
-- def ⦃ JoinSemilatticeMonoid lattice ⦄ = {!!}
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


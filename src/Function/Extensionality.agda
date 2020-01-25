{-# OPTIONS --exact-split --prop  #-}
module Function.Extensionality where

open import Axiom.FunctionExtensionality public

open import Universes
open import Proposition.Identity.Coercion
open import Function renaming (_$_ to _$'_)
open import Proof

het-fun-ext : 
  {f : (x : X) → A x}
  {f' : (y : Y) → B y}
  (p : X == Y)
  (q : ∀ x → f x == f' (coe p x))
  → ----------------------------
  f == f'
het-fun-ext {f = f}{f'}(Id.refl X) q = fun-ext λ x →
  proof f x
    === f' (coe (refl X) x) :by: q x
    === f' x                :by: ap f' $ coe-eval (refl X) x
  qed

het-==→~ :
  {f : (x : X) → A x}
  {g : (y : Y) → B y}
  (q : f == g)
  (p : X == Y)
  (p' : ∀ x → A x == B (coe p x))
  → -----------------
  ∀ x → f x == g (coe p x)
het-==→~ {A = A}{B = B}{f}{g} _ (Id.refl X) p' _ with p''
  where p'' : A == B
        p'' = fun-ext $ λ x →
          proof A x
            === B (coe (refl X) x) :by: p' x
            === B x                :by: ap B $ coe-eval (refl X) x
          qed
het-==→~ (Id.refl f)(Id.refl X) _  x | Id.refl A = ap f $ sym $ coe-eval (refl X) x

-- open import Logic

-- type== :
--   {X X' : 𝒰 ˙}{A : X → 𝒱 ˙}{A' : X' → 𝒱 ˙}
--   (p : ((x : X) → A x) == ((x : X') → A' x))
--   (x : X)
--   (f : Π A)
--   → -----------------------------------------
--   X == X'
-- type== p x f = {!coe-eval p f!}

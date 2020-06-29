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
  (q : ∀ x → f x Het.== f' (coe p x))
  → ----------------------------
  f Het.== f'
het-fun-ext {f = f}{f'}(Id.refl X) q = fun-ext λ x →
  proof f x
    het== f' (coe (refl X) x) :by: q x
    het== f' x                :by: ap f' $ coe-eval (refl X) x
  qed

het-==→~ :
  {f : (x : X) → A x}
  {g : (y : Y) → B y}
  (q : f Het.== g)
  (p : X == Y)
  (p' : ∀ x → A x == B (coe p x))
  → -----------------
  ∀ x → f x Het.== g (coe p x)
het-==→~ {X = X}{A = A}{B = B}{f}{g} q (Id.refl X) p' x = with' q p″ x
  where p″ : A Het.== B
        p″ = fun-ext $ λ x →
          proof A x
            === B (coe (refl X) x) :by: p' x [: _==_ ]
            het== B x              :by: ap B $ coe-eval (refl X) x
          qed
        with' :
          (q : f Het.== g)
          (p : A Het.== B)
          (x : X)
          → -------------------------------
          f x Het.== g (coe (Id.refl X) x)
        with' (Het.refl f)(Het.refl A) x =
          ap f $ isym $ coe-eval (Id.refl X) x

-- open import Logic

-- type== :
--   {X X' : 𝒰 ˙}{A : X → 𝒱 ˙}{A' : X' → 𝒱 ˙}
--   (p : ((x : X) → A x) == ((x : X') → A' x))
--   (x : X)
--   (f : Π A)
--   → -----------------------------------------
--   X == X'
-- type== p x f = {!coe-eval p f!}

{-# OPTIONS --exact-split --safe --prop  #-}
module Proof.Definition where

open import PropUniverses

open import Type.Sum using (Σ; _,_; pr₁; pr₂; _×_)
import Proposition.Identity as Identity
open import Relation.Binary hiding (_~_)

open import Proposition.Identity renaming (refl to Id-refl) public
open import Proposition.Identity.Homogeneous.Property public
open import Proposition.Function using (_$_) public
open import Function.Proof
  using (
    ap; ap2;
    Relating-all-==-het==; Relating-all-het==;
    Relating-2-all-==; Relating-2-all-het==;
    RelatingInjective; RelatingInjectiveHet)
  public
open Relation.Binary using (sym; refl) public
open import Relation.Binary.ReflexiveTransitiveClosure public

-- generalisation of symmetry
record IndexedSymmetric
    {X : 𝒰 ˙}
    {LevF : X → Universe}
    {F : (x : X) → LevF x ˙}
    {LevR : (x y : X) → Universe}
    (_R_ : ∀ {x y} → Rel (LevR x y) (F x) (F y)) : 𝒰ω
  where
  field
    isym : ∀ {x y}{x₁ : F x}{y₁ : F y}
      (p : x₁ R y₁)
      → ---------------
      y₁ R x₁

open IndexedSymmetric ⦃ … ⦄ public

instance
  IndexedSymmetricHet== : IndexedSymmetric {𝒰 ⁺}{F = λ x → x} Het._==_

isym ⦃ IndexedSymmetricHet== ⦄ (Het.refl x) = Het.refl x

-- generalisation of transitivity
record Composable 𝒵 (R : Rel 𝒯 X Y) (S : Rel 𝒮 Y Z) : 𝒰ω
  where
  field
      rel : Rel 𝒵 X Z
      compose : ∀ {x y z}(p : R x y) (q : S y z) → rel x z

instance
  Composable-==-== : {X : 𝒰 ˙} →
    Composable 𝒰 (_==_ {X = X}) _==_

Composable.rel Composable-==-== = _==_
Composable.compose Composable-==-== (Id-refl _) q = q

module MakeComposable (R : Rel 𝒲 X Y) where
  instance
    composable-R-== : Composable 𝒲 R _==_
    composable-==-R : Composable 𝒲 _==_ R

  Composable.rel composable-R-== = R
  Composable.compose composable-R-== p (Id-refl x) = p
  
  Composable.rel composable-==-R = R
  Composable.compose composable-==-R (Id-refl x) q = q

module MakeTransComposable
    (R : BinRel 𝒰 X)
    ⦃ p : Transitive R ⦄
    where
  open MakeComposable R public
  instance
    ComposableTrans : Composable 𝒰 R R

  Composable.rel ComposableTrans = R
  Composable.compose ComposableTrans = trans

module Composable-het== {X Y : 𝒰 ˙} where
  open MakeComposable (Het._==_ {X = X}{Y}) public
  instance
    Composable-Het==-Het== : {Z : 𝒰 ˙} →
      Composable 𝒰 (Het._==_ {X = X}{Y}) (Het._==_ {X = Y}{Z})

  Composable.rel Composable-Het==-Het== = Het._==_
  Composable.compose Composable-Het==-Het== (Het.refl _) q = q

infix 7 proof_
proof_ : (x : X) → x == x
proof_ = Id-refl

infix 5 _qed
_qed : (x : 𝑋) → 𝑋
x qed = x

infix 5 qed:
qed: : (𝑋 : 𝒰 ᵖ)(x : 𝑋) → 𝑋
qed: 𝑋 x = x

syntax qed: 𝑋 x = x qed[ 𝑋 ]

infixl 6 _〉_〉_:by:_
_〉_〉_:by:_ : {X : 𝒰 ˙} {Y : 𝒱 ˙} {Z : 𝒲 ˙}
  {x : X} {y : Y}
  {_R_ : Rel 𝒯 X Y}
  (p : x R y)
  (_S_ : Rel 𝒮 Y Z)
  (z : Z)
  (q : y S z)
  ⦃ c : Composable 𝒵 _R_ _S_ ⦄
  → -------------------------------------
  Composable.rel c x z
_〉_〉_:by:_ p r a q ⦃ c ⦄  = Composable.compose c p q

infixl 6 _===_:by:_ _het==_:by:_
_===_:by:_ :
  {x : X} {y : Y}
  {_R_ : Rel 𝒰 X Y}
  (p : x R y)
  (z : Y)
  (q : y == z)
  ⦃ c : Composable 𝒵 _R_ _==_ ⦄
  → -------------------------------------
  Composable.rel c x z
p === z :by: q = p 〉 _==_ 〉 z :by: q

_het==_:by:_ :
  {x : X} {y : Y}
  {_R_ : Rel 𝒰 X Y}
  (p : x R y)
  (z : Z)
  (q : y Het.== z)
  ⦃ c : Composable 𝒵 _R_ Het._==_ ⦄
  → -------------------------------------
  Composable.rel c x z
p het== z :by: q = p 〉 Het._==_ 〉 z :by: q

-- TODO: check if this actually works

structured-proof = λ {𝒰}(X : 𝒰 ˙) → X

{-# DISPLAY _qed x = structured-proof #-}

open import Function.Equivalence.Definition
open import Function.Property

injective-equiv :
  {f g : (x : X) → A x}
  ⦃ injective : Injective f ⦄
  (p : f ~ g)
  → ---------------------------
  Injective g
inj ⦃ injective-equiv {f = f}{g} f~g ⦄ {x}{y} gx==gy = inj (
  proof f x
    het== g x :by: f~g x
    het== g y :by: gx==gy
    het== f y :by: isym $ f~g y
  qed)

data Singleton {X Y : 𝒰 ˙}(x : X) : 𝒰 ˙ where
  _with==_ : (y : Y) (p : x Het.== y) → Singleton x

inspect : {X : 𝒰 ˙} (x : X) → Singleton x
inspect x = x with== Het.refl x

from-instance : ⦃ p : 𝑋 ⦄ → 𝑋
from-instance ⦃ p ⦄ = p

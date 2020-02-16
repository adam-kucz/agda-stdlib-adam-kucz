{-# OPTIONS --exact-split --safe --prop  #-}
module Proof where

open import PropUniverses

open import Type.Sum using (Σ; _,_; pr₁; pr₂; _×_)
import Proposition.Identity.Definition as Identity
open import Relation.Binary.Definition using (Rel)
open import Relation.Binary.Property using (Transitive; trans)

open import Proposition.Identity.Definition
  renaming (Idₚ to Id) hiding (refl) public
open import Proposition.Identity.Property public
open import Proposition.Identity.Function using (ap2) public
open import Proposition.Function using (_$_) public
open import Function.Proof
  using (ap; Relating-all-==; ap'; RRelating-all-==) public
open Relation.Binary.Property using (sym; refl) public

-- generalisation of symmetry
record StrongSymmetric
    {X : 𝒰 ˙}
    {LevF : X → Universe}
    {F : (x : X) → LevF x ˙}
    {LevR : (x y : X) → Universe}
    (_R_ : ∀ {x y} → Rel (LevR x y) (F x) (F y)) : 𝒰ω
  where
  field
    strong-sym : ∀ {x y}{x₁ : F x}{y₁ : F y}
      (p : x₁ R y₁)
      → ---------------
      y₁ R x₁

open StrongSymmetric ⦃ … ⦄ public

instance
  StrongSymmetric== : StrongSymmetric {𝒰 ⁺}{F = λ x → x} _==_

strong-sym ⦃ StrongSymmetric== ⦄ (Id.refl x) = refl x

-- generalisation of transitivity
record Composable 𝒵 (R : Rel 𝒯 X Y) (S : Rel 𝒮 Y Z) : 𝒰ω
  where
  field
      rel : Rel 𝒵 X Z
      compose : ∀ {x y z}(p : R x y) (q : S y z) → rel x z

instance
  Composable-==-== : ∀ {X Y Z : 𝒰 ˙} →
    Composable 𝒰 (_==_ {X = X}{Y}) (_==_ {X = Y}{Z})

Composable.rel Composable-==-== = _==_
Composable.compose Composable-==-== (Id.refl _) q = q

module MakeComposable (R : Rel 𝒲 X Y) where
  instance
    composable-R-== : Composable 𝒲 R _==_
    composable-==-R : Composable 𝒲 _==_ R

  Composable.rel composable-R-== = R
  Composable.compose composable-R-== p (Id.refl x) = p
  
  Composable.rel composable-==-R = R
  Composable.compose composable-==-R (Id.refl x) q = q

module TransMakeComposable
    (R : Rel 𝒱 X X) ⦃ p : Transitive R ⦄
    where
  instance
    composable-trans : Composable 𝒱 R R

  Composable.rel composable-trans = R
  Composable.compose composable-trans = trans

  open MakeComposable R public

infix 7 proof_
proof_ : {X : 𝒰 ˙} (x : X) → x == x
proof_ = Id.refl

infix 5 _qed
_qed : {X : 𝒰 ᵖ} (x : X) → X
x qed = x

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

infixl 6 _===_:by:_
_===_:by:_ : {X : 𝒰 ˙} {Y Z : 𝒱 ˙}
  {x : X} {y : Y}
  {_R_ : Rel 𝒯 X Y}
  (p : x R y)
  (z : Z)
  (q : y == z)
  ⦃ c : Composable 𝒵 _R_ _==_ ⦄
  → -------------------------------------
  Composable.rel c x z
p === z :by: q = p 〉 _==_ 〉 z :by: q

data Singleton {X Y : 𝒰 ˙}(x : X) : 𝒰 ˙ where
  _with==_ : (y : Y) (p : x == y) → Singleton x

inspect : {X : 𝒰 ˙} (x : X) → Singleton x
inspect x = x with== Id.refl x

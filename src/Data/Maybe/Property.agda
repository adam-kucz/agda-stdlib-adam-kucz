{-# OPTIONS --exact-split --safe #-}
module Data.Maybe.Property where

open import Data.Maybe.Definition

open import Universes
open import Type.Decidable
open import Proof

instance
  MaybeHasDecidableIdentity :
    ⦃ d== : HasDecidableIdentity X ⦄
    → ----------------------------------------
    HasDecidableIdentity (Maybe X)

MaybeHasDecidableIdentity {x = nothing}{nothing} = true (refl nothing)
MaybeHasDecidableIdentity {x = nothing}{just _} = false λ ()
MaybeHasDecidableIdentity {x = just x}{nothing} = false λ ()
MaybeHasDecidableIdentity {x = just x}{just y} with decide (x == y)
MaybeHasDecidableIdentity {x = just x}{just y} | true p = true (ap just p)
MaybeHasDecidableIdentity {x = just x}{just y} | false ¬p =
  false λ { (Id.refl (just x)) → ¬p (Id.refl x)}

open import Collection

instance
  MaybeCollection : {X : 𝒰 ˙} → Collection 𝒰 (Maybe X) X
  MaybeEmpty : Empty (Maybe X) X
  MaybeListable : {X : 𝒰 ˙} → Listable 𝒰 (Maybe X) X
  MaybeRemovable :
    ⦃ d : HasDecidableIdentity X ⦄
    → -----------------------------------
    Removable (Maybe X) X
  MaybeIntersection :
    ⦃ d : HasDecidableIdentity X ⦄
    → -----------------------------------
    Intersection (Maybe X) X

open import Data.List.Definition
open import Data.List.Collection
open import Logic
open import Logic.Proof

_∈_ ⦃ MaybeCollection ⦄ x nothing = Lift𝒰 ⊥
_∈_ ⦃ MaybeCollection ⦄ x (just y) = x == y
∅ ⦃ MaybeEmpty ⦄ = nothing
_∉∅ ⦃ MaybeEmpty ⦄ _ ()
collection ⦃ MaybeListable ⦄ = MaybeCollection
to-list ⦃ MaybeListable ⦄ nothing = []
to-list ⦃ MaybeListable ⦄ (just x) = [ x ]
⟶ (to-list-valid ⦃ MaybeListable ⦄ {just x}) (Id.refl x) = x∈x∷ []
⟵ (to-list-valid ⦃ MaybeListable ⦄ {just x}) (x∈x∷ []) = Id.refl x
remove ⦃ MaybeRemovable ⦄ x nothing = nothing
remove ⦃ MaybeRemovable ⦄ x (just y) = if y == x then ∅ else just y
⟶ (remove-valid ⦃ MaybeRemovable ⦃ d ⦄ ⦄ {_}{y}{just x}) p with d {x}{y}
⟶ (remove-valid MaybeRemovable) () | true (Id.refl _)
⟶ (remove-valid MaybeRemovable) (Id.refl x) | false ¬p =
  Id.refl x , ¬p
⟵ (remove-valid ⦃ MaybeRemovable ⦃ d ⦄ ⦄ {_}{y}{just x}) (Id.refl x , x≠y)
  with d {x}{y}
⟵ (remove-valid MaybeRemovable) (Id.refl x , x≠y) | true p = ↑ $ x≠y p
⟵ (remove-valid MaybeRemovable) (Id.refl x , x≠y) | false ¬p = Id.refl x
_∩_ ⦃ MaybeIntersection ⦄ nothing _ = nothing
_∩_ ⦃ MaybeIntersection ⦄ (just x) nothing = nothing
_∩_ ⦃ MaybeIntersection ⦄ (just x) (just y) =
  if x == y then just x else nothing
⟶ (∩-valid ⦃ MaybeIntersection ⦃ d ⦄ ⦄ {_}{just x}{just y}) p
  with d {x}{y}
⟶ (∩-valid MaybeIntersection) (Id.refl x) | true (Id.refl x) =
  Id.refl x , Id.refl x
⟵ (∩-valid ⦃ MaybeIntersection ⦃ d ⦄ ⦄ {_}{just x}{just x})
  (Id.refl x , Id.refl x) with d {x}{x}
⟵ (∩-valid MaybeIntersection) (Id.refl x , Id.refl x) | true p = Id.refl x
⟵ (∩-valid MaybeIntersection) (Id.refl x , Id.refl x) | false ¬p =
  ↑ $ ¬p $ Id.refl x


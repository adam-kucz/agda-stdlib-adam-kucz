{-# OPTIONS --safe --exact-split --prop  #-}
module Data.NonemptyList.Property where

open import Data.NonemptyList.Definition

open import PropUniverses
open import Collection

data member : (x : X)(l : NonemptyList X) → 𝒰₀ ᵖ where
  ∈[_] : (x : X) → member x [ x ]
  _∈head_ : (x : X)(t : NonemptyList X) → member x (x ∷ t)
  _∈⦅_∷_⦆ : (x h : X){t : NonemptyList X}(p : member x t) → member x (h ∷ t)

open import Collection.Definition

{-# DISPLAY member v l = v ∈ l #-}

open import Proposition.Decidable

instance
  NonemptyListCollection : Collection 𝒰₀ (NonemptyList X) X
  NonemptyListInsertable : Insertable (NonemptyList X) X
  NonemptyListNonemptyListable : Listable 𝒰₀ (NonemptyList X) X
  NonemptyListUnion : Union (NonemptyList X) X
  NonemptyListDecidable∈ :
    ⦃ d : HasDecidableIdentity X ⦄
    → ----------------------------------------
    ∀ {x : X}{l : NonemptyList X} → Decidable (x ∈ l)

_∈_ ⦃ NonemptyListCollection ⦄ = member

open import Logic
open import Proof

insert ⦃ NonemptyListInsertable ⦄ = _∷_
⟶ (insert-valid ⦃ NonemptyListInsertable ⦄) (x ∈⦅ h ∷ p ⦆) =
  ∨left p
⟶ (insert-valid ⦃ NonemptyListInsertable ⦄) (x ∈head t) =
  ∨right (refl x)
⟵ (insert-valid ⦃ NonemptyListInsertable ⦄ {x}{y}) (∨left p) =
  y ∈⦅ x ∷ p ⦆
⟵ (insert-valid ⦃ NonemptyListInsertable ⦄ {S = l})
  (∨right (Id.refl x)) = x ∈head l

open import Data.List renaming ([_] to [[_]])

collection ⦃ NonemptyListNonemptyListable ⦄ = NonemptyListCollection
to-list ⦃ NonemptyListNonemptyListable ⦄ [ x ] = [[ x ]]
to-list ⦃ NonemptyListNonemptyListable ⦄ (h ∷ t) = h ∷ to-list t
⟶ (to-list-valid ⦃ NonemptyListNonemptyListable ⦄) ∈[ x ] = x∈x∷ []
⟶ (to-list-valid ⦃ NonemptyListNonemptyListable ⦄) (x ∈head t) =
  x∈x∷ (to-list t)
⟶ (to-list-valid ⦃ NonemptyListNonemptyListable ⦄) (x ∈⦅ h ∷ p ⦆) =
  x∈tail h $ ⟶ to-list-valid p
⟵ (to-list-valid ⦃ NonemptyListNonemptyListable ⦄ {[ x ]})
  (x∈x∷ []) = ∈[ x ]
⟵ (to-list-valid ⦃ NonemptyListNonemptyListable ⦄ {h ∷ t})
  (x∈x∷ .(to-list t)) = h ∈head t 
⟵ (to-list-valid ⦃ NonemptyListNonemptyListable ⦄ {h ∷ t}{x})
  (x∈tail h q) = x ∈⦅ h ∷ ⟵ to-list-valid q ⦆ 

_∪_ ⦃ NonemptyListUnion ⦄ [ x ] l₁ = x ∷ l₁
_∪_ ⦃ NonemptyListUnion ⦄ (h ∷ l₀) l₁ = h ∷ (l₀ ∪ l₁)
⟶ (∪-valid ⦃ NonemptyListUnion ⦄ {S₀ = [ x' ]})
  (x' ∈head t) = ∨left ∈[ x' ]
⟶ (∪-valid ⦃ NonemptyListUnion ⦄ {S₀ = [ x' ]})
  (x ∈⦅ x' ∷ p ⦆) = ∨right p
⟶ (∪-valid ⦃ NonemptyListUnion ⦄ {S₀ = h ∷ l₀})
  (h ∈head .(l₀ ∪ _)) = ∨left $ h ∈head l₀
⟶ (∪-valid ⦃ NonemptyListUnion ⦄ {S₀ = h ∷ l₀})
  (x ∈⦅ h ∷ p ⦆) with ⟶ (∪-valid {S₀ = l₀}) p
⟶ (∪-valid NonemptyListUnion {S₀ = h ∷ l₀})
  (x ∈⦅ h ∷ p ⦆) | ∨left q = ∨left $ x ∈⦅ h ∷ q ⦆
⟶ (∪-valid NonemptyListUnion {S₀ = h ∷ l₀})
  (x ∈⦅ h ∷ p ⦆) | ∨right q = ∨right q
⟵ (∪-valid ⦃ NonemptyListUnion ⦄ {S₀ = [ x ]}{l₁})
  (∨left ∈[ x ]) = x ∈head l₁ 
⟵ (∪-valid ⦃ NonemptyListUnion ⦄ {S₀ = h ∷ l₀} {l₁})
  (∨left (h ∈head l₀)) = h ∈head (l₀ ∪ l₁)
⟵ (∪-valid ⦃ NonemptyListUnion ⦄ {S₀ = h ∷ l₀} {l₁})
  (∨left (x ∈⦅ h ∷ p ⦆)) = x ∈⦅ h ∷ ⟵ ∪-valid (∨left p) ⦆
⟵ (∪-valid ⦃ NonemptyListUnion ⦄ {x}{[ x' ]}{l₁}) (∨right q) =
  x ∈⦅ x' ∷ q ⦆
⟵ (∪-valid ⦃ NonemptyListUnion ⦄ {x}{h ∷ l₀}{l₁}) (∨right q) =
  x ∈⦅ h ∷ ⟵ (∪-valid {S₀ = l₀}) $ ∨right q ⦆

open import Proposition.Identity hiding (refl)

NonemptyListDecidable∈ {x = x} {[ x₁ ]} =
  dif x == x₁
    then (λ p → true (Id.coe (ap (λ — → x ∈ [ — ]) p) $ ∈[ x ]))
    else λ ¬p → false λ { ∈[ x ] → ¬p (refl x)}
NonemptyListDecidable∈ {x = x} {h ∷ l} with decide (x == h)
NonemptyListDecidable∈ {x = x} {h ∷ l}
  | true p = true (Id.coe (ap (λ — → x ∈ — ∷ l) p) (x ∈head l))
NonemptyListDecidable∈ {x = x} {h ∷ l}
  | false ¬p with NonemptyListDecidable∈ {x = x}{l}
NonemptyListDecidable∈ {x = x} {h ∷ l}
  | false ¬p | true q = true (x ∈⦅ h ∷ q ⦆)
NonemptyListDecidable∈ {x = x} {h ∷ l}
  | false ¬p | false ¬q =
  false (λ { (x ∈head t) → ¬p (refl x)
           ; (x ∈⦅ h ∷ q ⦆) → ¬q q})

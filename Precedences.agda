module Precedences where

-- Terms (200 - 100)

infixl 150 _∘_ -- Type.Transport
infixl 150 _∘_ -- Function

infixl 145 _ᶜ -- Collection.Subset

infixl 140 _*_ -- Data.Nat
infixl 130 _*_ -- Structure.Monoid
infixl 130 _+_ -- Data.Nat
infixl 130 _∙_ -- Structure.Semigroup
infixl 120 _⊓_ -- Data.Nat
infixl 120 _⊔_ -- Data.Nat

infixr 115 _∷_ -- Data.List
infixr 115 _∷_ -- Data.Vec
infixr 110 _!_[_] -- Data.List
infixr 110 _!_[_] -- Data.Vec
infixr 108 ⋃_ ⋂_ -- Collection.Operation
infixl 105 _++_ -- Collection
infixl 105 _++_ -- Data.List
infixl 105 _∪_ _`_ _⁻¹`_ -- Collection.Operation
infixl 105 _[_,_]`_ -- Type.Subset.Decidable
infixl 104 _∩_ -- Type.Subset.Operation

infixr 104 _<$>_ -- Data.Functor
infixl 103 _<*>_ -- Data.Applicative
infixr 100 _$_ -- Function

-- Types (60 - 50)

infix 57 _×_ -- Type.Sum
infix 55 _+_ -- Type.Sum
infix 51 _,_ -- Type.Sum
infix 50 _⟺_ -- Type.Transport
infix 50 _,_ -- Type.Transport

-- Logic formers (40 - 30)

infix 35 _∈_ -- Type.Subset
infix 35 _∈_ -- Collection
infix 35 _<_ -- Data.Nat.Order
infix 35 _≤_ -- Data.Nat.Order
infix 35 _<ₜ_ -- Data.Nat.Order
infix 35 _<ₛ_ -- Data.FinNat.Order
infix 35 _≤ₛ_ -- Data.FinNat.Order

infix 21 _≤ₛ_ -- Data.Relation.Property

-- Descriptive properties (20)

infix 20 _is-left-unit-of_ -- Operation.Binary
infix 20 _is-right-unit-of_ -- Operation.Binary
infix 20 _is-unit-of_ -- Operation.Binary

-- Equalities (19)

infix 19 _==_ -- Prop'.Identity.Definition
infix 19 _≠_ -- Prop'.Identity
infix 19 _~_ -- Function.Equivalence
infix 19 _~_ -- Relation.Equivalence
infix 19 _~_ -- Type.Quotient.Class

-- Logic (18 - 10)

infix 18 ¬_ -- Prop'.Empty
infixl 17 _∧_ -- Prop'.Sum
infixl 15 _∨_ -- Prop'.BinarySum
infix 11 _↔_ -- Logic
infixl 11 _,_ -- Prop'.Sum
infix 11 _,_ -- Prop'.Sum
infix 11 _,_ -- Prop'.Sum
infixl 11 _,_ -- Logic
infix 11 _,_ -- Operation.Property

-- Proof (10 - 5)

infix 7 proof_ -- Proof
infix 5 _qed -- Proof
infixl 6 _〉_〉_:by:_ _===_:by:_ _het==_:by:_ -- Proof

infix 4 have_:from:_ -- Prop'.Proof
infixl 3 _⟶_:by:_ -- Prop'.Proof

-- Universes (separate)

infix 1 _˙ -- Universes
infix 1 _ᵖ -- PropUniverses

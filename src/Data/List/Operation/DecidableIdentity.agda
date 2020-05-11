{-# OPTIONS --safe --exact-split --prop  #-}
open import PropUniverses
open import Proposition.Decidable

module Data.List.Operation.DecidableIdentity
  {X : 𝒰 ˙} ⦃ d : HasDecidableIdentity X ⦄
  where

  open import Data.Nat
  open import Data.Maybe
  open import Data.List.Definition
  open import Data.List.Collection
  open import Collection hiding (_~_)
  open import Logic
  open import Proof

  find : (x : X) (l : List X) → Maybe ℕ
  find x [] = nothing
  find x (h ∷ l) with decide (x == h)
  find x (h ∷ l) | true  _ = just 0
  find x (h ∷ l) | false _ with find x l
  find x (h ∷ l) | false _ | nothing = nothing
  find x (h ∷ l) | false _ | just x₁ = just x₁
  
  index : {x : X} {l : List X} (p : x ∈ l) → ℕ
  index {x = x} {h ∷ l} p with decide (x == h)
  index {x = x} {h ∷ l} p | true   x==h = 0
  index {x = x} {h ∷ l} p | false ¬x==h = suc (index (prev p))
    where open import Proposition.Empty
          prev : (p : x ∈ h ∷ l) → x ∈ l
          prev (x∈x∷ t) = ⊥-recursionₚ (x ∈ l) $ ¬x==h $ Id-refl x
          prev (x∈tail _ p) = p

  module Multiplicity where
    multiplicity : (x : X)(l : List X) → ℕ
    multiplicity x [] = 0
    multiplicity x (h ∷ l) with decide (x == h)
    multiplicity x (h ∷ l) | true  _ = suc (multiplicity x l)
    multiplicity x (h ∷ l) | false _ = multiplicity x l

    ∉→==0 : ∀{x : X}{l : List X}
      (p : x ∉ l) → multiplicity x l == 0
    ∉→==0 {l = []} p = Id-refl 0
    ∉→==0 {x}{h ∷ t} p with d {x}{h}
    ∉→==0 {x}{x ∷ t} p | true (Id-refl x) =
      ⊥-recursion _ $ p $ x∈x∷ t
    ∉→==0 {x}{h ∷ t} p | false ¬p =
      ∉→==0 λ p' → p $ x∈tail h p'

    open import Data.List.Property
    
    remove-invariant :
      {x y : X}
      (l : List X)
      (p : x ≠ y)
      → ----------------------------------------
      multiplicity x (remove y l) == multiplicity x l
    remove-invariant [] p = Id-refl 0
    remove-invariant {x}{y}(h ∷ t) p with d {x}{h} | d {h}{y}
    remove-invariant (h ∷ t) p
      | true (Id-refl h) | true x=y = ⊥-recursion _ $ p x=y
    remove-invariant (h ∷ t) p
      | true (Id-refl h) | false _ with d {h}{h}
    remove-invariant (h ∷ t) p
      | true (Id-refl h) | false _ | true _ =
      ap suc $ remove-invariant t p
    remove-invariant (h ∷ t) p
      | true (Id-refl h) | _ | false ¬h=h =
      ⊥-recursion _ $ ¬h=h $ Id-refl h
    remove-invariant {x}(h ∷ t) p
      | false _ | true (Id-refl h) = remove-invariant t p
    remove-invariant {x} {y} (h ∷ t) p
      | false x≠h | false h≠y with d {x}{h}
    remove-invariant (h ∷ t) p
      | false x≠h | false h≠y | true x=h = ⊥-recursion _ $ x≠h x=h
    remove-invariant (h ∷ t) p
      | false x≠h | false h≠y | false ¬p = remove-invariant t p

    open import Function.Proof
    open import Proposition.Permutation.Definition
    
    Relating-multiplicity-swap-== : {x : X} →
      Relating (multiplicity x) single-swap _==_
    rel-preserv ⦃ Relating-multiplicity-swap-== {x} ⦄ = go
      where go : {l₀ l₁ : List X}
              (p : single-swap l₀ l₁)
              → ----------------------------------------
              multiplicity x l₀ == multiplicity x l₁
            go (swap y z l) with d {x}{y}
            go (swap y z l) | true _ with d {x}{z}
            go (swap y z l) | true _ | true _ with d {x}{y}
            go (swap y z l) | true _ | true _ | true _ = Id-refl _
            go (swap y z l) | true x=y | true _ | false x≠y =
              ⊥-recursion _ $ x≠y x=y
            go (swap y z l) | true _ | false _ with d {x}{y}
            go (swap y z l) | true _ | false _ | true _ = Id-refl _
            go (swap y z l) | true x=y | false _ | false x≠y =
              ⊥-recursion _ $ x≠y x=y
            go (swap y z l) | false _ with d {x}{z}
            go (swap y z l) | false _ | true _ with d {x}{y}
            go (swap y z l) | false x≠y | true _ | true x=y =
              ⊥-recursion _ $ x≠y x=y
            go (swap y z l) | false _ | true _ | false _ = Id-refl _
            go (swap y z l) | false _ | false _ with d {x}{y}
            go (swap y z l) | false x≠y | false _ | true x=y =
              ⊥-recursion _ $ x≠y x=y
            go (swap y z l) | false _ | false _ | false _ = Id-refl _
            go (step y rab) with d {x}{y}
            go (step y rab) | true _ = ap suc $ go rab
            go (step y rab) | false ¬p = go rab

    instance
      Relating-multiplicity-~-== : {x : X} →
        Relating (multiplicity x) _~_ _==_

    rel-preserv ⦃ Relating-multiplicity-~-== ⦄ p =
      subrel ⦃ Subrelation-rtcR-R _==_ _ ⦄ $
      rel-preserv ⦃ Relating-rtc ⦃ Relating-multiplicity-swap-== ⦄ ⦄ p
      where open import Relation.Binary.ReflexiveTransitiveClosure.Transfer

  open Multiplicity using (multiplicity) public

  is-uniq : (l : List X) → 𝒰 ᵖ
  is-uniq l = ¬ ∃ λ (x : X) → 2 ≤ multiplicity x l
    where open import Data.Nat using (_≤_)

  open import Proposition.Sum
  open import Data.List.Insertable
  open import Data.List.Property

  recreate-is-uniq : (l : List X) → is-uniq (recreate l)
  recreate-is-uniq (h ∷ t) (x , p) with d {x}{h}
  recreate-is-uniq (x ∷ t) (x , s≤s p) | true (Id-refl x) with
    proof 1
      〉 _≤_ 〉 multiplicity x (remove x l') :by: p
      〉 _==_ 〉 0 :by: Multiplicity.∉→==0 $ x ∉remove l'
    qed
    where l' = from-list-uniq (x ∷ t) t
  recreate-is-uniq (x ∷ t) (x , s≤s p) | true (Id-refl x) | ()
  recreate-is-uniq (h ∷ t) (x , p) | false x≠h =
    recreate-is-uniq t (x ,
      (proof 2
         〉 _≤_ 〉 multiplicity x (remove h (from-list-uniq (h ∷ t) t))
           :by: p
         〉 _==_ 〉 multiplicity x (from-list-uniq (h ∷ t) t)
           :by: Multiplicity.remove-invariant (from-list-uniq (h ∷ t) t) x≠h 
         〉 _==_ 〉 multiplicity x (recreate t)
           :by: lemma t t
       qed))
    where lemma : ∀ l t →
            multiplicity x (from-list-uniq (h ∷ t) l) ==
            multiplicity x (from-list-uniq t l)
          lemma [] _ with d {x}{h}
          lemma [] _ | true x=h = ⊥-recursion _ $ x≠h x=h
          lemma [] _ | false ¬p = Id-refl _
          lemma (h' ∷ t') t with d {x}{h'}
          lemma (x ∷ t') t | true (Id-refl x) = ap suc (
            proof multiplicity x (remove x (from-list-uniq (h ∷ t) t'))
              === 0
                :by: Multiplicity.∉→==0 $ x
                     ∉remove (from-list-uniq (h ∷ t) t')
              === multiplicity x (remove x (from-list-uniq t t'))
                :by: sym $ Multiplicity.∉→==0 $
                     x ∉remove (from-list-uniq t t')
            qed)
          lemma (h' ∷ t') t | false ¬p =
            proof multiplicity x (remove h' (from-list-uniq (h ∷ t) t'))
              === multiplicity x (from-list-uniq (h ∷ t) t')
                :by: Multiplicity.remove-invariant (from-list-uniq (h ∷ t) t') ¬p
              === multiplicity x (from-list-uniq t t')
                :by: lemma t' t
              === multiplicity x (remove h' (from-list-uniq t t'))
                :by: sym $ Multiplicity.remove-invariant (from-list-uniq t t') ¬p
            qed

  uniq : (l : List X) →
    Σₚ λ (l' : List X) →
      (∀ {x : X}(p : x ∈ l) → x ∈ l') ∧
      is-uniq l'
  uniq l = recreate l , (⟵ recreate-prop , recreate-is-uniq l)




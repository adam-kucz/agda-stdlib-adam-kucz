{-# OPTIONS --exact-split --prop --safe  #-}
module Logic.Proof where

open import Logic.Basic
open import Logic.Iff

open import PropUniverses
open import Relation.Binary.Property

instance
  Symmetric∨ : Symmetric (_∨_ {𝒰})

  Symmetric∧ : Symmetric (_∧_ {𝒰})
  Transitive∧ : Transitive (_∧_ {𝒰})

sym ⦃ Symmetric∨ ⦄ (∨left p) = ∨right p
sym ⦃ Symmetric∨ ⦄ (∨right q) = ∨left q

sym ⦃ Symmetric∧ ⦄ (left , right) = right , left
trans ⦃ Transitive∧ ⦄ (left , _) (_ , right) = left , right

open import Proof

module WithUniverse {𝒰}{𝒱} where
  open MakeComposable (_↔_ {𝒰}{𝒱}) public
  instance
    Composable-↔-↔ :
      Composable (𝒰 ⊔ 𝒲) (_↔_ {𝒰}{𝒱}) (_↔_ {𝒱}{𝒲})
  Composable.rel Composable-↔-↔ = _↔_
  Composable.compose Composable-↔-↔ (x→y , y→x) (y→z , z→y) =
    (λ x → y→z (x→y x)) ,
    (λ z → y→x (z→y z))

instance
  IndexedSymmetric↔ : IndexedSymmetric {F = _ᵖ} _↔_

isym ⦃ IndexedSymmetric↔ ⦄ (x→y , y→x) = y→x , x→y

open import Function.Proof

instance
  Relating-∧-left-↔ : Relating (𝑋 ∧_) (_↔_ {𝒰}) _↔_
  Relating-∧-right-↔ : Relating (_∧ 𝑋) (_↔_ {𝒰}) _↔_
  Relating-∨-left-↔ : Relating (𝑋 ∨_) (_↔_ {𝒰}) _↔_
  Relating-∨-right-↔ : Relating (_∨ 𝑋) (_↔_ {𝒰}) _↔_
  Relating-2-∧ : Relating-2 (_∧_ {𝒰}{𝒱}) _↔_ _↔_ _↔_
  Relating-2-∨ : Relating-2 (_∨_ {𝒰}{𝒱}) _↔_ _↔_ _↔_

⟶ (rel-preserv ⦃ Relating-∧-left-↔ ⦄ A↔B) (x , a) = x , ⟶ A↔B a
⟵ (rel-preserv ⦃ Relating-∧-left-↔ ⦄ A↔B) (x , b) = x , ⟵ A↔B b

⟶ (rel-preserv ⦃ Relating-∧-right-↔ ⦄ A↔B) (a , x) = ⟶ A↔B a , x
⟵ (rel-preserv ⦃ Relating-∧-right-↔ ⦄ A↔B) (b , x) = ⟵ A↔B b , x

⟶ (rel-preserv ⦃ Relating-∨-left-↔ ⦄ A↔B) (∨left x) = ∨left x
⟶ (rel-preserv ⦃ Relating-∨-left-↔ ⦄ A↔B) (∨right b) = ∨right $ ⟶ A↔B b
⟵ (rel-preserv ⦃ Relating-∨-left-↔ ⦄ A↔B) (∨left x) = ∨left x
⟵ (rel-preserv ⦃ Relating-∨-left-↔ ⦄ A↔B) (∨right a) = ∨right $ ⟵ A↔B a

⟶ (rel-preserv ⦃ Relating-∨-right-↔ ⦄ A↔B) (∨right x) = ∨right x
⟶ (rel-preserv ⦃ Relating-∨-right-↔ ⦄ A↔B) (∨left b) = ∨left $ ⟶ A↔B b
⟵ (rel-preserv ⦃ Relating-∨-right-↔ ⦄ A↔B) (∨right x) = ∨right x
⟵ (rel-preserv ⦃ Relating-∨-right-↔ ⦄ A↔B) (∨left a) = ∨left $ ⟵ A↔B a

rel-preserv-2 ⦃ Relating-2-∧ ⦄ {X}{X'}{Y}{Y'} X↔X' Y↔Y' =
  proof X ∧ Y
    〉 _↔_ 〉 X' ∧ Y  :by: ap (_∧ Y) X↔X'  [: _↔_ ]
    〉 _↔_ 〉 X' ∧ Y' :by: ap (X' ∧_) Y↔Y'
  qed
rel-preserv-2 ⦃ Relating-2-∨ ⦄ {X}{X'}{Y}{Y'} X↔X' Y↔Y' =
  proof X ∨ Y
    〉 _↔_ 〉 X' ∨ Y  :by: ap (_∨ Y) X↔X'  [: _↔_ ]
    〉 _↔_ 〉 X' ∨ Y' :by: ap (X' ∨_) Y↔Y'
  qed

-↔-∧- : (p : 𝑋 → 𝑌) → 𝑋 ↔ 𝑋 ∧ 𝑌
⟶ (-↔-∧- p) x = x , p x
⟵ (-↔-∧- p) (x , _) = x

-↔-∨- : (p : 𝑌 → 𝑋) → 𝑋 ↔ 𝑋 ∨ 𝑌
⟶ (-↔-∨- p) x = ∨left x
⟵ (-↔-∨- p) (∨left x) = x
⟵ (-↔-∨- p) (∨right y) = p y

[∨]∧↔∧∨∧ : (𝑋 ∨ 𝑌) ∧ 𝑍 ↔ 𝑋 ∧ 𝑍 ∨ 𝑌 ∧ 𝑍
⟶ [∨]∧↔∧∨∧ (∨left x , z) = ∨left (x , z)
⟶ [∨]∧↔∧∨∧ (∨right y , z) = ∨right (y , z)
⟵ [∨]∧↔∧∨∧ (∨left (x , z)) = ∨left x , z
⟵ [∨]∧↔∧∨∧ (∨right (y , z)) = ∨right y , z

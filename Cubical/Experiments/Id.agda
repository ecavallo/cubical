{-# OPTIONS --cubical #-}
module Cubical.Experiments.Id where

open import Cubical.Foundations.Everything


module _ {ℓ ℓ'} {A : Type ℓ}
  (P : ∀ x y → x ≡ y → Type ℓ') (d : ∀ x → P x x refl)
  where

  J' : (φ : I) (x : A) (p : I → A [ φ ↦ (λ _ → x) ]) → P _ _ (λ i → outS (p i))
  J' φ x p =
    comp
      (λ j → P _ _ (λ k → filler j k))
      (λ j → λ {(φ = i1) → d x})
      (d (outS (p i0)))
    where
    filler : I → I → A
    filler j =
      hfill
        (λ k → λ
          { (j = i0) → outS (p i0)
          ; (j = i1) → outS (p k)
          ; (φ = i1) → x
          })
        (inS (outS (p i0)))

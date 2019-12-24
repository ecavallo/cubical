{-# OPTIONS --cubical --safe #-}
module Cubical.Experiments.MoreGroupoid where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws

private
  variable
    ℓ : Level
    A : Type ℓ
    x y z w : A

assoc' : (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
  → p ∙ q ∙ r ≡ (p ∙ q) ∙ r
assoc' p q r k i =
  hcomp
    (λ j → λ
      { (i = i0) → p i0
      ; (i = i1) →
        hcomp
          (λ l → λ
            { (j = i0) → q k
            ; (j = i1) → r l
            ; (k = i1) → r (j ∧ l)
            })
          (q (j ∨ k))
      })
    (compPath-filler p q k i)

experiment : Square {A = x ≡ x} refl (assoc' refl refl refl) (λ k → refl ∙ lUnit refl k) (λ k → rUnit refl k ∙ refl)
experiment {x = x} k m i =
  hcomp
    (λ j → λ
      { (i = i0) → x
      ; (i = i1) → lUnit {x = x} refl (k ∧ ~ m) j
      })
    (compPath-filler {x = x} refl refl (k ∧ m) i)

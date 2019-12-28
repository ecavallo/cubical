{-# OPTIONS --cubical --safe #-}
module Cubical.Experiments.MoreGroupoid where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws

-- compPath-filler' p q j i
-- j = 0 → (p ∙ q) i
-- j = 1 → q i
-- i = 0 → p j
-- i = 1 → q i1
compPath-filler' : ∀ {ℓ} {A : Type ℓ} {x y z : A} → x ≡ y → y ≡ z → I → I → A
compPath-filler' p q j i =
  hcomp
    (λ k → λ
      { (i = i0) → p j
      ; (i = i1) → q k
      ; (j = i1) → q (i ∧ k)
      })
    (p (i ∨ j))

assoc' : ∀ {ℓ} {A : Type ℓ} {x y z w : A}
  (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
  → p ∙ q ∙ r ≡ (p ∙ q) ∙ r
assoc' p q r k =
  (λ i → compPath-filler p q k i) ∙ (λ i → compPath-filler' q r k i)

squareToPath1 : ∀ {ℓ} {A : Type ℓ} {x y z : A} {r : x ≡ y} {p q : y ≡ z}
  → Square r p r q → p ≡ q
squareToPath1 {r = r} {p} {q} sq i j =
  hcomp
    (λ k → λ
      { (i = i0) → p (j ∧ k)
      ; (i = i1) → q j
      ; (j = i0) → p i0
      ; (j = i1) → p (i ∨ k)
      })
    (hcomp
      (λ k → λ
        { (i = i0) → r (j ∨ k)
        ; (i = i1) → q j
        ; (j = i0) → r (i ∨ k)
        ; (j = i1) → p i
        })
      (sq j i))

squareToPath0 : ∀ {ℓ} {A : Type ℓ} {x y z : A} {p q : x ≡ y} {r : y ≡ z} 
  → Square p r q r → p ≡ q
squareToPath0 sq i j = squareToPath1 (λ i j → sq (~ i) (~ j)) i (~ j)

rUnitCoh : ∀ {ℓ} {A : Type ℓ} {x y : A}
  → (p : x ≡ y) → rUnit (p ∙ refl) ≡ λ i → rUnit p i ∙ refl
rUnitCoh p = squareToPath1 (λ i j → rUnit (rUnit p i) j)

lUnitCoh : ∀ {ℓ} {A : Type ℓ} {x y : A}
  → (p : x ≡ y) → lUnit (refl ∙ p) ≡ λ i → refl ∙ lUnit p i
lUnitCoh p = squareToPath1 (λ i j → lUnit (lUnit p i) j)

assocRefl : ∀ {ℓ} {A : Type ℓ} {x : A}
  → Square {A = x ≡ x} refl (assoc' refl refl refl) (λ k → refl ∙ lUnit refl k) (λ k → rUnit refl k ∙ refl)
assocRefl {x = x} k m =
  rUnit {x = x} refl (k ∧ m) ∙ lUnit refl (k ∧ ~ m)

assocRefl' : ∀ {ℓ} {A : Type ℓ} {x : A}
  → Square {A = x ≡ x} refl (assoc' refl refl refl) (lUnit (refl ∙ refl)) (rUnit (refl ∙ refl))
assocRefl' {x = x} i j =
  hcomp
    (λ k → λ
      { (i = i0) → refl ∙ refl
      ; (i = i1) → assoc' refl refl refl j
      ; (j = i0) → lUnitCoh refl (~ k) i
      ; (j = i1) → rUnitCoh refl (~ k) i
      })
    (assocRefl i j)

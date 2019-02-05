-- This file derives some of the Cartesian Kan operations using transp
{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.CartesianKanOps where

open import Cubical.Core.Everything

coe0→1 : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1
coe0→1 A a = transp A i0 a

-- "coe filler"
coe0→i : ∀ {ℓ} (A : I → Set ℓ) (i : I) → A i0 → A i
coe0→i A i a = transp (λ j → A (i ∧ j)) (~ i) a

-- Check the equations for the coe filler
coe0→i1 : ∀ {ℓ} (A : I → Set ℓ) (a : A i0) → coe0→i A i1 a ≡ coe0→1 A a
coe0→i1 A a = refl

coe0→i0 : ∀ {ℓ} (A : I → Set ℓ) (a : A i0) → coe0→i A i0 a ≡ a
coe0→i0 A a = refl

-- coe backwards
coe1→0 : ∀ {ℓ} (A : I → Set ℓ) → A i1 → A i0
coe1→0 A a = transp (λ i → A (~ i)) i0 a

-- coe backwards filler
coe1→i : ∀ {ℓ} (A : I → Set ℓ) (i : I) → A i1 → A i
coe1→i A i a = transp (λ j → A (i ∨ ~ j)) i a

-- Check the equations for the coe backwards filler
coe1→i0 : ∀ {ℓ} (A : I → Set ℓ) (a : A i1) → coe1→i A i0 a ≡ coe1→0 A a
coe1→i0 A a = refl

coe1→i1 : ∀ {ℓ} (A : I → Set ℓ) (a : A i1) → coe1→i A i1 a ≡ a
coe1→i1 A a = refl

-- "squeezeNeg"
coei→0 : ∀ {ℓ} (A : I → Set ℓ) (i : I) → A i → A i0
coei→0 A i a = transp (λ j → A (i ∧ ~ j)) (~ i) a

coei0→0 : ∀ {ℓ} (A : I → Set ℓ) (a : A i0) → coei→0 A i0 a ≡ a
coei0→0 A a = refl

coei1→0 : ∀ {ℓ} (A : I → Set ℓ) (a : A i1) → coei→0 A i1 a ≡ coe1→0 A a
coei1→0 A a = refl

-- "master coe"
-- defined as the filler of coei→0, coe0→i, and coe1→i
-- unlike in cartesian cubes, we don't get coei→i = id definitionally
coei→j : ∀ {ℓ} (A : I → Set ℓ) (i j : I) → A i → A j
coei→j A i j a =
  fill A
    (λ j → λ { (i = i0) → coe0→i A j a
             ; (i = i1) → coe1→i A j a
             })
    (inc (coei→0 A i a))
    j

-- "squeeze"
-- this is just defined as the composite face of the master coe
coei→1 : ∀ {ℓ} (A : I → Set ℓ) (i : I) → A i → A i1
coei→1 A i a = coei→j A i i1 a

coei0→1 : ∀ {ℓ} (A : I → Set ℓ) (a : A i0) → coei→1 A i0 a ≡ coe0→1 A a
coei0→1 A a = refl

coei1→1 : ∀ {ℓ} (A : I → Set ℓ) (a : A i1) → coei→1 A i1 a ≡ a
coei1→1 A a = refl

-- equations for "master coe"
coei→i0 : ∀ {ℓ} (A : I → Set ℓ) (i : I) (a : A i) → coei→j A i i0 a ≡ coei→0 A i a
coei→i0 A i a = refl

coei0→i : ∀ {ℓ} (A : I → Set ℓ) (i : I) (a : A i0) → coei→j A i0 i a ≡ coe0→i A i a
coei0→i A i a = refl

coei→i1 : ∀ {ℓ} (A : I → Set ℓ) (i : I) (a : A i) → coei→j A i i1 a ≡ coei→1 A i a
coei→i1 A i a = refl

coei1→i : ∀ {ℓ} (A : I → Set ℓ) (i : I) (a : A i1) → coei→j A i1 i a ≡ coe1→i A i a
coei1→i A i a = refl

-- only non-definitional equation
coei→i : ∀ {ℓ} (A : I → Set ℓ) (i : I) (a : A i) → coei→j A i i a ≡ a
coei→i A i = coe0→i (λ i → (a : A i) → coei→j A i i a ≡ a) i (λ _ → refl)

-- do the same for fill

fill1→i : ∀ {ℓ} (A : ∀ i → Set ℓ)
       {φ : I}
       (u : ∀ i → Partial φ (A i))
       (u1 : A i1 [ φ ↦ u i1 ])
       ---------------------------
       (i : I) → A i
fill1→i A {φ = φ} u u1 i =
  comp (λ j → A (i ∨ ~ j))
       (λ j → λ { (φ = i1) → u (i ∨ ~ j) 1=1
                ; (i = i1) → ouc u1 })
       (inc {φ = φ ∨ i} (ouc {φ = φ} u1))

filli→0 : ∀ {ℓ} (A : ∀ i → Set ℓ)
       {φ : I}
       (u : ∀ i → Partial φ (A i))
       (i : I)
       (ui : A i [ φ ↦ u i ])
       ---------------------------
       → A i0
filli→0 A {φ = φ} u i ui =
  comp (λ j → A (i ∧ ~ j))
       (λ j → λ { (φ = i1) → u (i ∧ ~ j) 1=1
                ; (i = i0) → ouc ui })
       (inc {φ = φ ∨ ~ i} (ouc {φ = φ} ui))

filli→j : ∀ {ℓ} (A : ∀ i → Set ℓ)
       {φ : I}
       (u : ∀ i → Partial φ (A i))
       (i : I)
       (ui : A i [ φ ↦ u i ])
       ---------------------------
       (j : I) → A j [ φ ↦ u j ]
filli→j A {φ = φ} u i ui j =
  inc
    (fill A
      (λ j → λ { (φ = i1) → u j 1=1
               ; (i = i0) → fill A u ui j
               ; (i = i1) → fill1→i A u ui j
               })
      (inc (filli→0 A u i ui))
      j)

filli→i : ∀ {ℓ} (A : ∀ i → Set ℓ)
       {φ : I}
       (u : ∀ i → Partial φ (A i))
       (i : I)
       (ui : A i [ φ ↦ u i ])
       ---------------------------
       → (ouc (filli→j A u i ui i) ≡ ouc ui) [ φ ↦ (λ {(φ = i1) → refl}) ]
filli→i A {φ = φ} u i ui =
  inc
    (fill1→i
      (λ k →
        fill A
          (λ j → λ { (φ = i1) → u j 1=1
                   ; (i = i0) → fill A u (inc (fill (λ _ → A i0) (λ _ w → u i0 w) ui k)) j
                   ; (i = i1) → ouc (filli→j A u (~ k) (inc (fill (λ l → A (~ l)) (λ l w → u (~ l) w) ui k)) j)
                   })
          (inc (filli→0 A u (i ∧ ~ k) (inc (fill (λ l → A (i ∧ ~ l)) (λ l w → u (i ∧ ~ l) w) ui k))))
          (i ∧ ~ k)
          ≡
          fill (λ l → A (i ∧ ~ l)) (λ l w → u (i ∧ ~ l) w) ui k)
      (λ k → (λ {(φ = i1) → refl}))
      (inc refl)
      i0)

-- We can reconstruct fill from hfill, coei→j, and the path coei→i ≡ id.
-- The definition does not rely on the computational content of the coei→i path.
fill' : ∀ {ℓ} (A : I → Set ℓ)
       {φ : I}
       (u : ∀ i → Partial φ (A i))
       (u0 : A i0 [ φ ↦ u i0 ])
       ---------------------------
       (i : I) → A i [ φ ↦ u i ]
fill' A {φ = φ} u u0 i =
  inc (hcomp (λ j → λ {(φ = i1) → coei→i A i (u i 1=1) j; (i = i0) → coei→i A i (ouc u0) j}) t)
  where
  t : A i
  t = hfill {φ = φ} (λ j v → coei→j A j i (u j v)) (inc (coe0→i A i (ouc u0))) i

fill'-cap :  ∀ {ℓ} (A : I → Set ℓ)
             {φ : I}
             (u : ∀ i → Partial φ (A i))
             (u0 : A i0 [ φ ↦ u i0 ])
             ---------------------------
             → ouc (fill' A u u0 i0) ≡ ouc (u0)
fill'-cap A u u0 = refl
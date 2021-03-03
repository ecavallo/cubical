{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Foundations.Equiv.IsoToEquivSub where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws

isEquiv→isIso : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B}
  → isEquiv f → isIso f
isEquiv→isIso ise .fst = invIsEq ise
isEquiv→isIso ise .snd .fst = secIsEq ise
isEquiv→isIso ise .snd .snd = retIsEq ise

module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (φ : I)
  {f : A → B}
  (isEq : Partial φ (isEquiv f))
  (isIso : isIso f [ φ ↦ (λ u → isEquiv→isIso (isEq u)) ])
  where

  private
    g = outS isIso .fst
    s = outS isIso .snd .fst
    t = outS isIso .snd .snd

  private
    module _ (b : B) (a : A) (p : f a ≡ b) where

      fill₀ : I → I → A
      fill₀ i =
        hfill
          (λ k → λ
            { (i = i0) → g b
            ; (i = i1) → t (g b) k
            })
          (inS (g (s b (~ i))))

      fill₁ : I → I → A
      fill₁ i =
        hfill
          (λ k → λ
            { (i = i0) → g b
            ; (i = i1) → t a k
            })
          (inS (g (p (~ i))))

      antisq : I → I → I → Partial φ A
      antisq i j k = λ {(φ = i1) →
        hfill
          (λ k → λ
            { (i = i0) → fill₀ j k
            ; (i = i1) → fill₁ j k
            ; (j = i0) → g b
            ; (j = i1) → t (isEq 1=1 .equiv-proof b .snd (a , p) i .fst) k
            })
          (inS (g (isEq 1=1 .equiv-proof b .snd (a , p) i .snd (~ j))))
          k
        }

      fill₂ : I → I → A
      fill₂ i =
        hfill
          (λ k → λ
            { (i = i0) → fill₀ k i1
            ; (i = i1) → fill₁ k i1
            ; (φ = i1) → antisq i k i1 1=1
            })
          (inS (g b))

      q : g b ≡ a
      q i = fill₂ i i1

      sq : I → I → A
      sq i j =
        hcomp
          (λ k → λ
            { (i = i0) → fill₀ j (~ k)
            ; (i = i1) → fill₁ j (~ k)
            ; (j = i0) → g b
            ; (j = i1) → t (q i) (~ k)
            ; (φ = i1) → antisq i j (~ k) 1=1
            })
          (fill₂ i j)

      sq₁ : I → I → B
      sq₁ i j =
        hcomp
          (λ k → λ
            { (i = i0) → s (s b (~ j)) k
            ; (i = i1) → s (p (~ j)) k
            ; (j = i0) → s b k
            ; (j = i1) → s (f (q i)) k
            ; (φ = i1) → s (isEq 1=1 .equiv-proof b .snd (a , p) i .snd (~ j)) k
            })
          (f (sq i j))
  
  isoToEquivSub : A ≃ B
  isoToEquivSub .fst = f
  isoToEquivSub .snd .equiv-proof b .fst .fst = g b
  isoToEquivSub .snd .equiv-proof b .fst .snd = s b
  isoToEquivSub .snd .equiv-proof b .snd (a , p) i .fst = q b a p i
  isoToEquivSub .snd .equiv-proof b .snd (a , p) i .snd j = sq₁ b a p i (~ j)

  test : PartialP {a = ℓ-max ℓ ℓ'} φ (λ {(φ = i1) → isoToEquivSub .snd .equiv-proof ≡ isEq 1=1 .equiv-proof})
  test = λ {(φ = i1) → refl}


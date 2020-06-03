{-

Weird idea

Proofs of groupoid laws inspired by CCHM identity types and transp

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Experiments.GroupoidLaws where

open import Cubical.Foundations.Prelude hiding (_∙_)

private
  variable
    ℓ : Level
    A : Type ℓ
    x y z w v : A

module WithCofs where

  conc : (φ ψ : I) {a : A}
    (p : (i : I) → A [ ~ i ∨ φ ↦ (λ _ → a) ])
    (q : (i : I) → A [ ~ i ∨ ψ ↦ (λ _ → outS (p i1)) ])
    → outS (p i0) ≡ outS (q i1)
  conc φ ψ p q i =
    hcomp
      (λ j → λ
        { (i = i0) → outS (p i0)
        ; (i = i1) → outS (q j)
        ; (φ = i1) → outS (q (i ∧ j))
        ; (ψ = i1) → outS (p i)
        })
      (outS (p i))

  rUnit : (φ : I) {a : A} (p : (i : I) → A [ ~ i ∨ φ ↦ (λ _ → a) ])
    → conc φ i0 p (λ _ → inS (outS (p i1))) ≡ (λ i → outS (p i))
  rUnit φ p j = conc φ j p (λ _ → inS (outS (p i1)))

  lUnit : (ψ : I) {a : A} (q : (i : I) → A [ ~ i ∨ ψ ↦ (λ _ → a) ])
    → conc i0 ψ (λ _ → inS a) q ≡ (λ i → outS (q i))
  lUnit ψ q j = conc j ψ (λ _ → inS (outS (q i0))) q

  rCancel : (φ : I) {a : A} (p : (i : I) → A [ ~ i ∨ φ ↦ (λ _ → a) ])
    → conc φ φ p ((λ i → inS (outS (p (~ i))))) ≡ refl
  rCancel φ p j =
    conc (φ ∨ j) (φ ∨ j) (λ i → inS (outS (p (i ∧ ~ j)))) (λ i → inS (outS (p (~ i ∧ ~ j))))

  lCancel : (φ : I) {a : A} (p : (i : I) → A [ ~ i ∨ φ ↦ (λ _ → a) ])
    → conc φ φ ((λ i → inS (outS (p (~ i))))) p ≡ refl
  lCancel φ p j =
    conc (φ ∨ j) (φ ∨ j) (λ i → inS (outS (p (~ i ∨ j)))) (λ i → inS (outS (p (i ∨ j))))

  assoc : (φ ψ ξ : I) {a : A}
    (p : (i : I) → A [ ~ i ∨ φ ↦ (λ _ → a) ])
    (q : (i : I) → A [ ~ i ∨ ψ ↦ (λ _ → outS (p i1)) ])
    (r : (i : I) → A [ ~ i ∨ ξ ↦ (λ _ → outS (q i1)) ])
    → conc φ (ψ ∧ ξ) p (λ i → inS (conc ψ ξ q r i))
    ≡ conc (φ ∧ ψ) ξ (λ i → inS (conc φ ψ p q i)) r
  assoc φ ψ ξ p q r j =
    conc (φ ∧ (ψ ∨ ~ j)) ((ψ ∨ j) ∧ ξ)
      (λ i → inS (conc φ (ψ ∨ ~ j) p (λ i → inS (outS (q (i ∧ j)))) i))
      (λ i → inS (conc (ψ ∨ j) ξ (λ i → inS (outS (q (i ∨ j)))) r i) )

  triangle : (φ ψ : I) {a : A}
    (p : (i : I) → A [ ~ i ∨ φ ↦ (λ _ → a) ])
    (q : (i : I) → A [ ~ i ∨ ψ ↦ (λ _ → outS (p i1)) ])
    → Square
      (assoc φ i0 ψ p (λ _ → inS (outS (p i1))) q)
      (λ _ → conc φ ψ p q)
      (λ j → conc φ (ψ ∧ j) p (λ i → inS (lUnit ψ q j i)))
      (λ j → conc (φ ∧ j) ψ (λ i → inS (rUnit φ p j i)) q)
  triangle φ ψ p q j =
    assoc φ j ψ p (λ _ → inS (outS (p i1))) q

  PentagonType : (φ ψ ξ χ : I) {a : A}
    (p : (i : I) → A [ ~ i ∨ φ ↦ (λ _ → a) ])
    (q : (i : I) → A [ ~ i ∨ ψ ↦ (λ _ → outS (p i1)) ])
    (r : (i : I) → A [ ~ i ∨ ξ ↦ (λ _ → outS (q i1)) ])
    (s : (i : I) → A [ ~ i ∨ χ ↦ (λ _ → outS (r i1)) ])
    → Type _
  PentagonType φ ψ ξ χ p q r s =
    Square
      (conc (φ ∧ ψ ∧ ξ ∧ χ) (φ ∧ ψ ∧ ξ ∧ χ)
        (λ j → inS (assoc φ ψ (ξ ∧ χ) p q (λ i → inS (conc ξ χ r s i)) j))
        (λ j → inS (assoc (φ ∧ ψ) ξ χ (λ i → inS (conc φ ψ p q i)) r s j)))
      (assoc φ (ψ ∧ ξ) χ p (λ i → inS (conc ψ ξ q r i)) s)
      (λ j → conc φ (ψ ∧ ξ ∧ χ) p (λ i → inS (assoc ψ ξ χ q r s j i)))
      (λ j → conc (φ ∧ ψ ∧ ξ) χ (λ i → inS (assoc φ ψ ξ p q r (~ j) i)) s)

  pentagon : (φ ψ ξ χ : I) {a : A}
    (p : (i : I) → A [ ~ i ∨ φ ↦ (λ _ → a) ])
    (q : (i : I) → A [ ~ i ∨ ψ ↦ (λ _ → outS (p i1)) ])
    (r : (i : I) → A [ ~ i ∨ ξ ↦ (λ _ → outS (q i1)) ])
    (s : (i : I) → A [ ~ i ∨ χ ↦ (λ _ → outS (r i1)) ])
    → PentagonType φ ψ ξ χ p q r s
  pentagon φ ψ ξ χ p q r s =
    transp
      (λ k →
        PentagonType (φ ∨ ~ k) ψ ξ (χ ∨ ~ k)
          (λ i → inS (outS (p (i ∨ ~ k))))
          q r
          (λ i → inS (outS (s (i ∧ k)))))
      (φ ∧ ψ ∧ ξ ∧ χ)
      (transp 
        (λ k →
          PentagonType i1 (ψ ∨ ~ k) (ξ ∨ ~ k) i1
            (λ _ → inS (outS (q (~ k))))
            (λ i → inS (outS (q (i ∨ ~ k))))
            (λ i → inS (outS (r (i ∧ k))))
            (λ _ → inS (outS (r k))))
        (ψ ∧ ξ)
        refl)

_⁻¹ : (x ≡ y) → (y ≡ x)
p ⁻¹ = sym p

infix 40 _⁻¹

_∙_ : x ≡ y → y ≡ z → x ≡ z
p ∙ q = WithCofs.conc i0 i0 (λ i → inS (p i)) λ i → inS (q i)

rUnit : (p : x ≡ y) → p ∙ refl ≡ p
rUnit p = WithCofs.rUnit i0 (λ i → inS (p i))

lUnit : (p : x ≡ y) → refl ∙ p ≡ p
lUnit p = WithCofs.lUnit i0 (λ i → inS (p i))

rCancel : (p : x ≡ y) → p ∙ p ⁻¹ ≡ refl
rCancel {x = x} p = WithCofs.rCancel i0 (λ i → inS (p i))

lCancel : (p : x ≡ y) → p ⁻¹ ∙ p ≡ refl
lCancel p = WithCofs.lCancel i0 (λ i → inS (p i))

assoc : (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) →
  p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r
assoc p q r = WithCofs.assoc i0 i0 i0 (λ i → inS (p i)) (λ i → inS (q i)) (λ i → inS (r i))

triangle : (p : x ≡ y) (q : y ≡ z)
  → Square
    (assoc p refl q)
    (λ _ → p ∙ q)
    (cong (p ∙_) (lUnit q))
    (cong (_∙ q) (rUnit p))
triangle p q = WithCofs.triangle i0 i0 (λ i → inS (p i)) (λ i → inS (q i))

pentagon : (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) (s : w ≡ v)
  → Square
    (assoc p q (r ∙ s) ∙ assoc (p ∙ q) r s)
    (assoc p (q ∙ r) s)
    (cong (p ∙_) (assoc q r s))
    (cong (_∙ s) (sym (assoc p q r)))
pentagon p q r s =
  WithCofs.pentagon i0 i0 i0 i0 (λ i → inS (p i)) (λ i → inS (q i)) (λ i → inS (r i)) (λ i → inS (s i))

import Cubical.Foundations.GroupoidLaws as GL

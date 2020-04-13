{-# OPTIONS --cubical #-}
module Cubical.Experiments.Equivariant where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
import Cubical.Data.Empty as ⊥
open import Cubical.Data.Fin hiding (elim)
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Nat.Order

[] : Fin 0 → I
[] (k , less) with ¬-<-zero less
[] (k , less) | ()

infixr 20 _∷_

_∷_ : ∀ {n} → I → (Fin n → I) → (Fin (suc n) → I)
(i ∷ f) (zero , less) = i
(i ∷ f) (suc k , less) = f (k , <-k+-cancel less)

cnx∧ : ∀ {n} → (Fin n → I) → I → (Fin n → I)
cnx∧ i k f = i f ∧ k

-- n-ary equivariant composition from CCHM/OP-style composition for Dedekind cubes.
-- (Some reversals occur in this definition, but only to simulate composition 1→0

module _ (n : ℕ) where

  module Fill {ℓ} (A : (Fin n → I) → Type ℓ) {φ : I}
    (u : ∀ i → Partial φ (A i))
    (i : Fin n → I)
    (a : A i [ φ ↦ u i ])
    where

    ⇒ : ∀ j → A j [ φ ↦ u j ]
    ⇒ j = inS
      (comp
        (λ k → A (cnx∧ j k))
        (λ k → λ {(φ = i1) → u (cnx∧ j k) 1=1})
        (comp
          (λ k → A (cnx∧ i (~ k)))
          (λ k → λ {(φ = i1) → u (cnx∧ i (~ k)) 1=1})
          (outS a)))

    cap : (outS (⇒ i) ≡ outS a) [ φ ↦ (λ {(φ = i1) → refl}) ]
    cap = inS
      (λ l →
        comp
          (λ k → A (cnx∧ i (k ∨ l)))
          (λ k → λ
            { (φ = i1) → u (cnx∧ i (k ∨ l)) 1=1
            ; (l = i1) → outS a
            })
          (comp
            (λ k → A (cnx∧ i (~ k ∨ l)))
            (λ k → λ
              { (φ = i1) → u (cnx∧ i (~ k ∨ l)) 1=1
              ; (l = i1) → outS a
              })
            (outS a)))

  module Coe {ℓ} (A : (Fin n → I) → Type ℓ) (i : Fin n → I) (a : A i)
    where

    module F = Fill A {φ = i0} (λ _ → λ ()) i (inS a)

    ⇒ : ∀ j → A j
    ⇒ j = outS (F.⇒ j)

    cap : (⇒ i) ≡ a
    cap = outS F.cap

-- deriving J from equivariant composition in the usual way

module PathJ {A : Type₀} (C : (I → A) → Type₀) (d : ∀ a → (C (λ _ → a))) where

  elim : ∀ p → C p
  elim p =
    Coe.⇒ 1
      (λ k → C (λ i → face' (k fzero) i))
      (λ _ → i0)
      (d (p i0))
      (λ _ → i1)
    where
    module Face (k : I) =
      Fill 1
        (λ _ → A)
        (λ l → λ
          { (k = i0) → p i0
          ; (k = i1) → p (l fzero)
          })
        (λ _ → i0)
        (inS (p i0))

    face' : I → I → A
    face' k l = outS
      (Fill.⇒ 1
        (λ _ → A)
        (λ m → λ
          { (k = i0) → p i0
          ; (k = i1) → p l
          ; (l = i0) → outS (Face.cap k) (m fzero)
          })
        (λ _ → i0)
        (inS (outS (Face.⇒ k (λ _ → l))))
        (λ _ → i1))

  onRefl : ∀ a → elim (λ _ → a) ≡ d a
  onRefl a j =
    outS
      (Fill.⇒ 1
        (λ k → C (λ i → face' (k fzero) i))
        (λ k → λ {(j = i1) → d a})
        (λ _ → i0)
        (inS (d a))
        (λ _ → i1))
    where
    module Face (k : I) =
      Fill 1
        (λ _ → A)
        (λ l → λ
          { (k = i0) → a
          ; (k = i1) → a
          ; (j = i1) → a
          })
        (λ _ → i0)
        (inS a)

    face' : I → I → A
    face' k l = outS
      (Fill.⇒ 1
        (λ _ → A)
        (λ m → λ
          { (k = i0) → a
          ; (k = i1) → a
          ; (l = i0) → outS (Face.cap k) (m fzero)
          ; (j = i1) → a
          })
        (λ _ → i0)
        (inS (outS (Face.⇒ k (λ _ → l))))
        (λ _ → i1))

-- J for squares. Using equivariance of the Kan operations, we can also define J
-- for n-cubes in an equivariant way, although Cubical Agda isn't expressive
-- enough to let us write it down except in concrete cases.

module SquareJ {A : Type₀} (C : (I → I → A) → Type₀) (d : ∀ a → C (λ _ _ → a)) where

  elim : ∀ α → C α
  elim α =
    Coe.⇒ 2
      (λ k → C (λ i₀ i₁ → face' (k fzero) (k (fsuc fzero)) i₀ i₁))
      (λ _ → i0)
      (d (α i0 i0))
      (λ _ → i1)
    where
    module Face (k₀ k₁ : I) =
      Fill 2
        (λ _ → A)
        (λ l → λ
          { (k₀ = i0) (k₁ = i0) → α i0 i0
          ; (k₀ = i1) (k₁ = i1) → α (l fzero) (l (fsuc fzero))
          })
        (λ _ → i0)
        (inS (α i0 i0))

    face' : I → I → I → I → A
    face' k₀ k₁ l₀ l₁ = outS
      (Fill.⇒ 1
        (λ _ → A)
        (λ m → λ
          { (k₀ = i0) (k₁ = i0) → α i0 i0
          ; (k₀ = i1) (k₁ = i1) → α l₀ l₁
          ; (l₀ = i0) (l₁ = i0) → outS (Face.cap k₀ k₁) (m fzero)
          })
        (λ _ → i0)
        (inS (outS (Face.⇒ k₀ k₁ (l₀ ∷ l₁ ∷ []))))
        (λ _ → i1))

  onRefl : ∀ a → elim (λ _ _ → a) ≡ d a
  onRefl a j =
    outS
      (Fill.⇒ 2
        (λ k → C (λ i₀ i₁ → face' (k fzero) (k (fsuc fzero)) i₀ i₁))
        (λ k → λ { (j = i1) → d a })
        (λ _ → i0)
        (inS (d a))
        (λ _ → i1))
    where
    module Face (k₀ k₁ : I) =
      Fill 2
        (λ _ → A)
        (λ l → λ
          { (k₀ = i0) (k₁ = i0) → a
          ; (k₀ = i1) (k₁ = i1) → a
          ; (j = i1) → a
          })
        (λ _ → i0)
        (inS a)

    face' : I → I → I → I → A
    face' k₀ k₁ l₀ l₁ = outS
      (Fill.⇒ 1
        (λ _ → A)
        (λ m → λ
          { (k₀ = i0) (k₁ = i0) → a
          ; (k₀ = i1) (k₁ = i1) → a
          ; (l₀ = i0) (l₁ = i0) → outS (Face.cap k₀ k₁) (m fzero)
          ; (j = i1) → a
          })
        (λ _ → i0)
        (inS (outS (Face.⇒ k₀ k₁ (l₀ ∷ l₁ ∷ []))))
        (λ _ → i1))

private
  -- equivariance test
  test₀ : {A : Type₀} (C : (I → I → A) → Type₀)
    (d : ∀ a → C (λ _ _ → a))
    (α : I → I → A)
    → SquareJ.elim C d α ≡ SquareJ.elim (λ β → C (λ i j → β j i)) d (λ j i → α i j)
  test₀ C d α = refl

-- We can use J for n-cubes as a convenient way to define connections that
-- satisfy the necessary equations.

-- The definitions here don't actually satisfy the equations; this is because of
-- two issues.

-- (1) Coercion in a square type in Cubical Agda doesn't commute with flipping
-- the square along its diagonal. The coercion could be redefined so that this
-- does hold (or we could expand things out and do it manually, but then the
-- idea is less clear).

-- (2) We won't get equations like p (i ∧ i) = p i. For this we would need
-- diagonal cofibrations. With diagonal cofibrations, we could ensure these in the
-- same way we ensure the face equations.


-- And.elim p i₀ i₁ ≈ p (i₀ ∧ i₁)
--
-- The equations we'd need to hold, besides the face equations, are
--
-- And.elim p i₀ i₁ = And.elim p i₁ i₀
-- And.elim p i i = p i
--
-- So far we don't use equivariance at all.
module And {A : Type₀} =
  PathJ {A = A} (λ p → Square refl (λ i → p i) refl (λ i → p i)) (λ _ → refl)


-- TernaryAnd.elim p i₀ i₁ i₂ ≈ p (i₀ ∧ i₁ ∧ i₂)
--
-- The equations we'd need to hold, besides the face equations, are
--
-- TernaryAnd.elim p i₀ i₁ i₂ = TernaryAnd.elim p i₁ i₀ i₂ (and other permutations)
-- TernaryAnd.elim p i i i₂ = And.elim p i i₂ (and other diagonals)
--
-- This still does not require equivariant composition.
module TernaryAnd {A : Type₀} =
  PathJ {A = A}
    (λ p →
      Cube
        refl
        (And.elim p)
        refl
        (And.elim p)
        (refl {x = refl {x = p i0}})
        (And.elim p))
    (λ a →
      -- this transport could of course be replaced with a Coe.⇒ but Agda will
      -- have a harder time checking that
      transport⁻
        (λ t →
          Cube
            refl
            (And.onRefl a t)
            refl
            (And.onRefl a t)
            (refl {x = refl {x = a}})
            (And.onRefl a t))
        refl)


-- And².elim α i₀ i₁ j₀ j₁ ≈ α (i₀ ∧ i₁) (j₀ ∧ j₁)
--
-- The equations we'd need to hold, besides the face equations, are
--
-- And².elim α i₀ i₁ j₀ j₁ = And².elim α i₁ i₀ j₀ j₁ (likewise for j)
-- And².elim α i₀ i₁ j₀ j₁ = And².elim (λ j i → α i j) j₀ j₁ i₀ i₁
-- And².elim α i i j₀ j₁ = And.elim (α i) j₀ j₁ (likewise for j)
--
-- The second equation is the one for which we use equivariance of composition/J
module And² {A : Type₀} =
  SquareJ {A = A}
    (λ α → SquareP
      (λ i₀ i₁ → Square
        (λ _ → And.elim (λ i → α i i0) i₀ i₁)
        (λ j → And.elim (λ i → α i j) i₀ i₁)
        (λ _ → And.elim (λ i → α i i0) i₀ i₁)
        (λ j → And.elim (λ i → α i j) i₀ i₁))
      (λ _ → And.elim (λ j → α i0 j))
      (λ i → And.elim (λ j → α i j))
      (λ _ → And.elim (λ j → α i0 j))
      (λ i → And.elim (λ j → α i j)))
    (λ a →
      transport⁻
        (λ t →
          SquareP
            (λ i₀ i₁ → Square
              (λ _ → And.onRefl a t i₀ i₁)
              (λ _ → And.onRefl a t i₀ i₁)
              (λ _ → And.onRefl a t i₀ i₁)
              (λ _ → And.onRefl a t i₀ i₁))
            (λ _ → And.onRefl a t)
            (λ _ → And.onRefl a t)
            (λ _ → And.onRefl a t)
            (λ _ → And.onRefl a t))
        refl)
   

-- We can repeat this recipe for arbitrary α : Iⁿ → A and f : Iᵐ → Iⁿ where f is
-- built out of connections. To make sure this commute with degeneracies, we need
--
-- weaken (connect α f) = connect (weaken α) (f ⊗ I).
--
-- To make sure this holds, first rewrite f as (f' ⊗ Iᵏ) : Iᵐ⁻ᵏ ⊗ Iᵏ → Iⁿ⁻ᵏ ⊗ Iᵏ
-- in a maximal way and then follow the recipe using f'

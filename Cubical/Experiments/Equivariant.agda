{-# OPTIONS --cubical --safe #-}
module Cubical.Experiments.Equivariant where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Fin

module Binary where

  fill→ : ∀ {ℓ} (A : I → I → Type ℓ) {φ : I}
    (u : ∀ i₀ i₁ → Partial φ (A i₀ i₁))
    (i₀ i₁ : I)
    (a : A i₀ i₁ [ φ ↦ u i₀ i₁ ])
    (j₀ j₁ : I) → A j₀ j₁
  fill→ A {φ} u i₀ i₁ a j₀ j₁ =
    comp
      (λ k → A (j₀ ∧ k) (j₁ ∧ k))
      (λ k → λ { (φ = i1) → u (j₀ ∧ k) (j₁ ∧ k) 1=1})
      (comp
        (λ k → A (i₀ ∧ ~ k) (i₁ ∧ ~ k))
        (λ k → λ { (φ = i1) → u (i₀ ∧ ~ k) (i₁ ∧ ~ k) 1=1 })
        (outS a))

  fillCap : ∀ {ℓ} (A : I → I → Type ℓ) {φ : I}
    (u : ∀ i₀ i₁ → Partial φ (A i₀ i₁))
    (i₀ i₁ : I)
    (a : A i₀ i₁ [ φ ↦ u i₀ i₁ ])
    → (fill→ A u i₀ i₁ a i₀ i₁ ≡ outS a)
  fillCap A {φ} u i₀ i₁ a l =
    comp
      (λ k → A (i₀ ∧ (k ∨ l)) (i₁ ∧ (k ∨ l)))
      (λ k → λ
        { (φ = i1) → u (i₀ ∧ (k ∨ l)) (i₁ ∧ (k ∨ l)) 1=1
        ; (l = i1) → outS a
        })
      (comp
        (λ k → A (i₀ ∧ (~ k ∨ l)) (i₁ ∧ (~ k ∨ l)))
        (λ k → λ
          { (φ = i1) → u (i₀ ∧ (~ k ∨ l)) (i₁ ∧ (~ k ∨ l)) 1=1
          ; (l = i1) → outS a
          })
        (outS a))

  -- this needs to hold by reflexivity
  fillCapTube : ∀ {ℓ} (A : I → I → Type ℓ)
    (u : ∀ i₀ i₁ → Partial i1 (A i₀ i₁))
    (i₀ i₁ : I)
    (a : A i₀ i₁ [ i1 ↦ u i₀ i₁ ])
    → fillCap A u i₀ i₁ a ≡ refl
  fillCapTube A u i₀ i₁ a = refl

  -- this needs to hold by reflexivity
  equivariance : ∀ {ℓ} (A : I → I → Type ℓ) {φ : I}
    (u : ∀ i₀ i₁ → Partial φ (A i₀ i₁))
    (i₀ i₁ : I)
    (a : A i₀ i₁ [ φ ↦ u i₀ i₁ ])
    (j₀ j₁ : I)
    → fill→ A u i₀ i₁ a j₀ j₁ ≡ fill→ (λ x₀ x₁ → A x₁ x₀) (λ x₀ x₁ → u x₁ x₀) i₁ i₀ a j₁ j₀
  equivariance A u i₀ i₁ a j₀ j₁ = refl

  -- this presumably also should hold by reflexivity
  capEquivariance : ∀ {ℓ} (A : I → I → Type ℓ) {φ : I}
    (u : ∀ i₀ i₁ → Partial φ (A i₀ i₁))
    (i₀ i₁ : I)
    (a : A i₀ i₁ [ φ ↦ u i₀ i₁ ])
    → fillCap A u i₀ i₁ a ≡ fillCap (λ x₀ x₁ → A x₁ x₀) (λ x₀ x₁ → u x₁ x₀) i₁ i₀ a
  capEquivariance A u i₀ i₁ a = refl

module Finite where

  cnx∧ : ∀ {n} → (Fin n → I) → I → (Fin n → I)
  cnx∧ i k f = i f ∧ k 

  fill→ : ∀ {ℓ n} (A : (Fin n → I) → Type ℓ) {φ : I}
    (u : ∀ i → Partial φ (A i))
    (i : Fin n → I)
    (a : A i [ φ ↦ u i ])
    → ∀ j → A j
  fill→ A {φ} u i a j =
    comp
      (λ k → A (cnx∧ j k))
      (λ k → λ {(φ = i1) → u (cnx∧ j k) 1=1})
      (comp
        (λ k → A (cnx∧ i (~ k)))
        (λ k → λ {(φ = i1) → u (cnx∧ i (~ k)) 1=1})
        (outS a))

  fillCap : ∀ {ℓ n} (A : (Fin n → I) → Type ℓ) {φ : I}
    (u : ∀ i → Partial φ (A i))
    (i : Fin n → I)
    (a : A i [ φ ↦ u i ])
    → fill→ A u i a i ≡ outS a
  fillCap A {φ} u i a l =
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
        (outS a))

  -- this needs to hold by reflexivity
  fillCapTube : ∀ {ℓ n} (A : (Fin n → I) → Type ℓ)
    (u : ∀ i → Partial i1 (A i))
    (i : Fin n → I)
    (a : A i [ i1 ↦ u i ])
    → fillCap A u i a ≡ refl
  fillCapTube A u i a = refl

{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Structures.Macro where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma

open import Cubical.Structures.Constant
open import Cubical.Structures.Pointed
open import Cubical.Structures.NAryOp
open import Cubical.Structures.Parameterized

data Desc : Typeω where
  cst : ∀ {ℓ} → Type ℓ → Desc
  var : Desc
  join : Desc → Desc → Desc
  param : ∀ {ℓ} → (A : Type ℓ) → Desc → Desc
  op : Desc → Desc

ℓ-desc : Level → Desc → Level
ℓ-desc ℓ (cst {ℓ = ℓ'} x) = ℓ'
ℓ-desc ℓ var = ℓ
ℓ-desc ℓ (join d₀ d₁) = ℓ-max (ℓ-desc ℓ d₀) (ℓ-desc ℓ d₁)
ℓ-desc ℓ (param {ℓ = ℓ'} A d) = ℓ-max ℓ' (ℓ-desc ℓ d)
ℓ-desc ℓ (op d) = ℓ-max ℓ (ℓ-desc ℓ d)

macro-structure : ∀ {ℓ} (d : Desc) → Type ℓ → Type (ℓ-desc ℓ d)
macro-structure (cst A) X = A
macro-structure var X = X
macro-structure (join d₀ d₁) X = macro-structure d₀ X × macro-structure d₁ X
macro-structure (param A d) X = A → macro-structure d X
macro-structure (op d) X = X → macro-structure d X

macro-iso : ∀ {ℓ} (d : Desc) → StrIso {ℓ} (macro-structure d) (ℓ-desc ℓ d)
macro-iso (cst A) = constant-iso A
macro-iso var = pointed-iso
macro-iso (join d₀ d₁) = join-iso (macro-iso d₀) (macro-iso d₁)
macro-iso (param A d) = parameterized-iso A λ _ → macro-iso d
macro-iso (op d) = unaryFunIso (macro-iso d)

macro-is-SNS : ∀ {ℓ} (d : Desc) → SNS {ℓ} (macro-structure d) (macro-iso d)
macro-is-SNS (cst A) = constant-is-SNS A
macro-is-SNS var = pointed-is-SNS
macro-is-SNS (join d₀ d₁) = join-SNS (macro-iso d₀) (macro-is-SNS d₀) (macro-iso d₁) (macro-is-SNS d₁)
macro-is-SNS (param A d) = Parameterized-is-SNS A (λ _ → macro-iso d) (λ _ → macro-is-SNS d)
macro-is-SNS (op d) = unaryFunSNS (macro-iso d) (macro-is-SNS d)

-- For example:

private
  variable
    ℓ : Level

open import Cubical.Data.Nat
    
module _ (A : Type ℓ) where

 -- a multi set structure inspired bei Okasaki
 multi-set-structure : Type ℓ → Type ℓ
 multi-set-structure X = X × (A → X → X) × (A → X → ℕ)

 Multi-Set : Type (ℓ-suc ℓ)
 Multi-Set = TypeWithStr ℓ multi-set-structure

 multi-set-iso : StrIso multi-set-structure ℓ
 multi-set-iso =
   macro-iso (join var (join (param A (op var)) (param A (op (cst ℕ)))))

 Multi-Set-is-SNS : SNS {ℓ₁ = ℓ} multi-set-structure multi-set-iso
 Multi-Set-is-SNS =
   macro-is-SNS (join var (join (param A (op var)) (param A (op (cst ℕ)))))

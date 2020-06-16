{-# OPTIONS --cubical --no-import-sorts --no-exact-split --safe #-}
module Cubical.Structures.MaybeRemark where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ₀ ℓ₁ ℓ₁' : Level

-- Consider first the structure X ↦ Maybe X.
-- There are two natural ways to define structured isomorphism for this structure.
-- Both of these are standard/univalent, so in particular they're equivalent.
-- However, iso₁ is more convenient to use.

module X↦MaybeX where

  structure : Type ℓ → Type ℓ
  structure X = Maybe X


  iso₁ :  StrIso structure ℓ
  iso₁ (X , ox) (Y , oy) e = map-Maybe (e .fst) ox ≡ oy

  iso₂ :  StrIso structure ℓ
  iso₂ (X , nothing) (Y , nothing) e = Lift Unit
  iso₂ (X , nothing) (Y , just _) e = Lift ⊥
  iso₂ (X , just _) (Y , nothing) e = Lift ⊥
  iso₂ (X , just x) (Y , just y) e = e .fst x ≡ y

-- We also have both these options for a structure like X ↦ Maybe (A × X).
-- Note that the structure X ↦ A × X inside the Maybe has a functorial action, which we use in the
-- iso₁-style definition but can avoid in iso₂. Again, iso₁ is more convenient in practice.

module X↦Maybe[A×X] (A : Type ℓ) where

  structure : Type ℓ → Type ℓ
  structure X = Maybe (X × A)

  iso₁ :  StrIso structure ℓ
  iso₁ (X , ox) (Y , oy) e = map-Maybe (map-fst (e .fst)) ox ≡ oy

  iso₂ :  StrIso structure ℓ
  iso₂ (X , nothing) (Y , nothing) e = Lift Unit
  iso₂ (X , nothing) (Y , just _) e = Lift ⊥
  iso₂ (X , just _) (Y , nothing) e = Lift ⊥
  iso₂ (X , just (x , a₀)) (Y , just (y , a₁)) e = (e .fst x ≡ y) × (a₀ ≡ a₁)

-- For the general case of X ↦ Maybe (S X), we do not know that S is functorial, so we only have
-- the second option. Consider for example X ↦ Maybe (X → X).

module X↦Maybe[X→X] where

  structure : Type ℓ → Type ℓ
  structure X = Maybe (X → X)

  iso₁ :  StrIso structure ℓ
  iso₁ (X , ox) (Y , oy) e = map-Maybe {!no functorial action!} ox ≡ oy

  iso₂ :  StrIso structure ℓ
  iso₂ (X , nothing) (Y , nothing) e = Lift Unit
  iso₂ (X , nothing) (Y , just _) e = Lift ⊥
  iso₂ (X , just _) (Y , nothing) e = Lift ⊥
  iso₂ (X , just f) (Y , just g) e = ∀ x → e .fst (f x) ≡ g (e .fst x)


-- So the functorial version is easier to use, but doesn't always work.

-- In general, whenever we have a structure S with a functorial action, we get standard/univalent notion of
-- structure along the lines of iso₁.

import Cubical.Structures.Functorial

-- On the other hand, any time we have a structure S, we have a standard/univalent notion of structure for
-- X ↦ Maybe (S X) along the lines of iso₂.

import Cubical.Structures.Maybe

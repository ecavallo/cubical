{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.Test where

open import Cubical.Data.Int.Base
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.Foundations.Everything

open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.WedgeConnectivity

open import Cubical.HITs.Nullification.Base
open import Cubical.HITs.SetTruncation.Base
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp.Base
open import Cubical.HITs.Truncation.Base
open import Cubical.HITs.Truncation as Trunc

open import Cubical.ZCohomology.Base

private
  variable
    ℓ : Level

module Rot {A : Type ℓ} (a₀ : A) (n : ℕ) (c : isConnected (suc (suc n)) A) where

  2n+4 = (2 + n) + (2 + n)

  σ : (a : A) → north ≡ north
  σ a = merid a ∙ merid a₀ ⁻¹

  σ' : (a : A) → south ≡ south
  σ' a = merid a₀ ⁻¹ ∙ merid a

  rotSquareA : (a : A)
    → PathP (λ i → typ (Ω (Susp A , merid a₀ i))) (σ a) (σ' a)
  rotSquareA a i j =
    hcomp
      (λ k → λ
        { (i = i0) → compPath-filler (merid a) (merid a₀ ⁻¹) k j
        ; (i = i1) → compPath-filler' (merid a₀ ⁻¹) (merid a) k j
        ; (j = i0) → merid a₀ (i ∧ k)
        ; (j = i1) → merid a₀ (i ∨ ~ k)
        })
      (merid a j)

  rotSquareB : (b : A)
    → PathP (λ i → typ (Ω (Susp A , merid b i))) (σ a₀) (σ' a₀)
  rotSquareB b i j =
    hcomp
      (λ k → λ
        { (i = i0) → rCancel (merid a₀) (~ k) j
        ; (i = i1) → lCancel (merid a₀) (~ k) j
        ; (j = i0) → merid b i
        ; (j = i1) → merid b i
        })
      (merid b i)

  P : (a b : A) → Type ℓ
  P a b =
    PathP (λ i → typ (Ω (∥ Susp A ∥ 2n+4 , ∣ merid b i ∣))) (cong′ ∣_∣ (σ a)) (cong′ ∣_∣ (σ' a))

  rotSquare : (a b : A) → P a b
  rotSquare =
    WedgeConnectivity.extension (suc n) (suc n)
      (A , a₀) c (A , a₀) c
      (λ a b → P a b ,
        subst
          (λ l → isOfHLevel l (P a b))
          (+-suc n (suc n))
          (isOfHLevelPathP' (n + (2 + n)) (isOfHLevelTrunc 2n+4 _ _) _ _))
      (λ a i j → ∣ rotSquareA a i j ∣)
      (λ b i j → ∣ rotSquareB b i j ∣)
      {!!}

  rotMerid : (a : A) (s : Susp A) → typ (Ω (∥ Susp A ∥ 2n+4 , ∣ s ∣))
  rotMerid a north = cong′ ∣_∣ (σ a)
  rotMerid a south = cong′ ∣_∣ (σ' a)
  rotMerid a (merid b i) = rotSquare a b i

  rotMeridTrunc : (a : A) → (t : ∥ Susp A ∥ 2n+4) → t ≡ t
  rotMeridTrunc a =
    Trunc.elim (λ _ → isOfHLevelPath 2n+4 (isOfHLevelTrunc 2n+4) _ _) (rotMerid a)

  equiv : (a : A) (i : I) → ∥ Susp A ∥ 2n+4 ≃ ∥ Susp A ∥ 2n+4
  equiv a i =
    isoToEquiv
      (iso
        (λ t → rotMeridTrunc a t i)
        (λ t → rotMeridTrunc a t (~ i))
        (λ t j → homotopySymInv (rotMeridTrunc a) t j i)
        (λ t j → homotopySymInv (rotMeridTrunc a) t j (~ i)))

module Test {A : Type ℓ} (a₀ : A) (n : ℕ) (c : isConnected (suc (suc n)) A) where

  2n+4 = (2 + n) + (2 + n)

  module R = Rot a₀ n c

  Code' : Susp (Susp A) → Type ℓ
  Code' north = ∥ Susp A ∥ 2n+4
  Code' south = ∥ Susp A ∥ 2n+4
  Code' (merid north i) = ∥ Susp A ∥ 2n+4
  Code' (merid south i) = ∥ Susp A ∥ 2n+4
  Code' (merid (merid a j) i) =
    Glue (∥ Susp A ∥ 2n+4) λ
      { (i = i0) → _ , R.equiv a i0
      ; (i = i1) → _ , R.equiv a i0
      ; (j = i0) → _ , R.equiv a i0
      ; (j = i1) → _ , R.equiv a i
      }

  Code : ∥ Susp (Susp A) ∥ suc 2n+4 → Type ℓ
  Code t =
    Trunc.rec
      {B = TypeOfHLevel ℓ 2n+4}
      (isOfHLevelTypeOfHLevel 2n+4)
      (λ s → Code' s , {!!})
      t
      .fst

  encode : ∀ t → ∣ north ∣ ≡ t → Code t
  encode t p = subst Code p ∣ north ∣

  decode' : ∀ s → Code' s → Path (∥ Susp (Susp A) ∥ suc 2n+4) ∣ north ∣ ∣ s ∣
  decode' north =
    Trunc.rec (isOfHLevelTrunc (suc 2n+4) _ _)
      (λ s → cong′ ∣_∣ (merid s ∙ merid north ⁻¹))
  decode' south =
    Trunc.rec (isOfHLevelTrunc (suc 2n+4) _ _)
      (λ s → cong′ ∣_∣ (merid s))
  decode' (merid s i) =
    {!!}

  decode : ∀ c → Code c → Path (∥ Susp (Susp A) ∥ suc 2n+4) ∣ north ∣ c
  decode =
    Trunc.elim
      (λ _ → isOfHLevelΠ (suc 2n+4) λ _ → isOfHLevelPath (suc 2n+4) (isOfHLevelTrunc (suc 2n+4)) _ _)
      decode'

  encodeRefl : encode ∣ north ∣ refl ≡ ∣ north ∣
  encodeRefl = transportRefl ∣ north ∣

  decodeEncode : ∀ p → decode ∣ north ∣ (encode ∣ north ∣ p) ≡ p
  decodeEncode =
    J (λ y p → decode y (encode y p) ≡ p)
      (cong (decode _) encodeRefl ∙ cong (cong′ ∣_∣) (rCancel (merid north)))

  encodeDecode : ∀ c → encode ∣ north ∣ (decode ∣ north ∣ c) ≡ c
  encodeDecode = Trunc.elim (λ _ → isOfHLevelPath 2n+4 (isOfHLevelTrunc 2n+4) _ _) lemma
    where
    lem : ∀ s → subst Code' (merid s) ∣ north ∣ ≡ ∣ s ∣
    lem north = refl
    lem south = cong′ ∣_∣ (merid a₀)
    lem (merid a i) =
      {!!}

    lemma : ∀ s → subst Code' (merid s ∙ merid north ⁻¹) ∣ north ∣ ≡ ∣ s ∣
    lemma s = {!!}

  final : typ (Ω (∥ Susp (Susp A) ∥ suc 2n+4 , ∣ north ∣)) ≃ ∥ Susp A ∥ 2n+4
  final = isoToEquiv (iso (encode ∣ north ∣) (decode ∣ north ∣) encodeDecode decodeEncode)

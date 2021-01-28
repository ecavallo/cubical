
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Displayed.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma

open import Cubical.Relation.Binary

private
  variable
    ℓA ℓA' ℓ≅A ℓB ℓB' ℓ≅B ℓC ℓ≅C : Level

record UARel (A : Type ℓA) (ℓ≅A : Level) : Type (ℓ-max ℓA (ℓ-suc ℓ≅A)) where
  no-eta-equality
  constructor uarel
  field
    _≅_ : A → A → Type ℓ≅A
    ua : (a a' : A) → (a ≅ a') ≃ (a ≡ a')
  ρ : (a : A) → a ≅ a
  ρ a = invEq (ua a a) refl

open BinaryRelation

-- another constructor for UARel using contractibility of relational singletons
make-𝒮 : {A : Type ℓA} {ℓ≅A : Level} {_≅_ : A → A → Type ℓ≅A}
          (ρ : isRefl _≅_) (contrTotal : contrRelSingl _≅_) → UARel A ℓ≅A
UARel._≅_ (make-𝒮 {_≅_ = _≅_} _ _) = _≅_
UARel.ua (make-𝒮 {_≅_ = _≅_} ρ c) = contrRelSingl→isUnivalent _≅_ ρ c

record DUARel {A : Type ℓA} {ℓ≅A : Level} (𝒮-A : UARel A ℓ≅A)
              (B : A → Type ℓB) (ℓ≅B : Level) : Type (ℓ-max (ℓ-max ℓA ℓB) (ℓ-max ℓ≅A (ℓ-suc ℓ≅B))) where
  no-eta-equality
  constructor duarel
  open UARel 𝒮-A

  field
    _≅ᴰ⟨_⟩_ : {a a' : A} → B a → a ≅ a' → B a' → Type ℓ≅B
    uaᴰ : {a : A} → (b b' : B a) → (b ≅ᴰ⟨ ρ a ⟩ b') ≃ (b ≡ b')
  ρᴰ : {a : A} → (b : B a) → b ≅ᴰ⟨ ρ a ⟩ b
  ρᴰ {a} b = invEq (uaᴰ b b) refl

make-𝒮ᴰ : {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
          {B : A → Type ℓB}
          (_≅ᴰ⟨_⟩_ : {a a' : A} → B a → UARel._≅_ 𝒮-A a a' → B a' → Type ℓ≅B)
          (ρᴰ : {a : A} → isRefl _≅ᴰ⟨ UARel.ρ 𝒮-A a ⟩_)
          (contrTotal : (a : A) → contrRelSingl _≅ᴰ⟨ UARel.ρ 𝒮-A a ⟩_)
          → DUARel 𝒮-A B ℓ≅B
DUARel._≅ᴰ⟨_⟩_ (make-𝒮ᴰ _≅ᴰ⟨_⟩_ ρᴰ contrTotal) = _≅ᴰ⟨_⟩_
DUARel.uaᴰ (make-𝒮ᴰ {𝒮-A = 𝒮-A} _≅ᴰ⟨_⟩_ ρᴰ contrTotal) {a} b b'
  = contrRelSingl→isUnivalent (_≅ᴰ⟨ UARel.ρ 𝒮-A a ⟩_) (ρᴰ {a}) (contrTotal a) b b'

private
  total : {A : Type ℓA} {ℓ≅A : Level} {𝒮-A : UARel A ℓ≅A}
          {B : A → Type ℓB} {ℓ≅B : Level}
          (𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B)
          → UARel (Σ A B) (ℓ-max ℓ≅A ℓ≅B)
  total {A = A} {ℓ≅A = ℓ≅A} {𝒮-A = 𝒮-A} {B = B} {ℓ≅B = ℓ≅B} 𝒮ᴰ-B =
    make-𝒮 ρΣ c
    where
      open UARel 𝒮-A
      open DUARel 𝒮ᴰ-B
      _≅Σ_ : Σ A B → Σ A B → Type (ℓ-max ℓ≅A ℓ≅B)
      (a , b) ≅Σ (a' , b') = Σ[ p ∈ a ≅ a' ] (b ≅ᴰ⟨ p ⟩ b')
      ρΣ : isRefl _≅Σ_
      ρΣ (a , b) = ρ a , ρᴰ b
      c : contrRelSingl _≅Σ_
      c (a , b) = cab , h
        where
          hA : contrRelSingl _≅_
          hA = isUnivalent→contrRelSingl _≅_ ua
          cab : relSinglAt _≅Σ_ (a , b)
          cab = (a , b) , ρΣ (a , b)
          hB : contrRelSingl (λ c c' → c ≅ᴰ⟨ ρ a ⟩ c')
          hB = isUnivalent→contrRelSingl _ uaᴰ
          g : (b' : B a) (q : b ≅ᴰ⟨ ρ a ⟩ b') → cab ≡ ((a , b') , ρ a , q)
          g b' q = J (λ w _ → cab ≡ ((a , fst w) , ρ a , snd w))
                     refl (isContr→isProp (hB b) (b , ρᴰ b) (b' , q))
          k : (a' : A) (p : a ≅ a') (b' : B a') (q : b ≅ᴰ⟨ p ⟩ b') → cab ≡ ((a' , b') , (p , q))
          k a' p = J (λ w _ → (b' : B (fst w)) (q : b ≅ᴰ⟨ snd w ⟩ b') → cab ≡ ((fst w , b') , (snd w , q)))
                     g (isContr→isProp (hA a) (a , ρ a) (a' , p))
          h : (w : relSinglAt _≅Σ_ (a , b)) → cab ≡ w
          h ((a' , b') , (p , q)) = k a' p b' q


-- total using copatterns
∫ : {A : Type ℓA} {ℓ≅A : Level} {𝒮-A : UARel A ℓ≅A}
        {B : A → Type ℓB} {ℓ≅B : Level}
        (𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B)
        → UARel (Σ A B) (ℓ-max ℓ≅A ℓ≅B)
UARel._≅_ (∫ 𝒮ᴰ-B) = UARel._≅_ (total 𝒮ᴰ-B)
UARel.ua (∫ 𝒮ᴰ-B) = UARel.ua (total 𝒮ᴰ-B)



Lift-𝒮ᴰ : {A : Type ℓA} (𝒮-A : UARel A ℓ≅A)
        {B : A → Type ℓB}
        (𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B)
        {C : A → Type ℓC}
        (𝒮ᴰ-C : DUARel 𝒮-A C ℓ≅C)
        → DUARel (∫ 𝒮ᴰ-C) (λ (a , _) → B a) ℓ≅B
DUARel._≅ᴰ⟨_⟩_ (Lift-𝒮ᴰ 𝒮-A 𝒮ᴰ-B 𝒮ᴰ-C)  b (pa , _) b' = b ≅ᴰ⟨ pa ⟩ b'
  where
    open DUARel 𝒮ᴰ-B
-- should use alternate constructor
DUARel.uaᴰ (Lift-𝒮ᴰ 𝒮-A 𝒮ᴰ-B 𝒮ᴰ-C) = {!!}


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
    ℓ ℓA ℓA' ℓ≅A ℓB ℓB' ℓ≅B ℓC ℓ≅C : Level

record UARel (A : Type ℓA) (ℓ≅A : Level) : Type (ℓ-max ℓA (ℓ-suc ℓ≅A)) where
  no-eta-equality
  constructor uarel
  field
    _≅_ : A → A → Type ℓ≅A
    ua : (a a' : A) → (a ≅ a') ≃ (a ≡ a')
  ρ : (a : A) → a ≅ a
  ρ a = invEq (ua a a) refl
  ≅→≡ : {a a' : A} (p : a ≅ a') → a ≡ a'
  ≅→≡ {a} {a'} p = equivFun (ua a a') p
  ≡→≅ : {a a' : A} (p : a ≡ a') → a ≅ a'
  ≡→≅ {a} {a'} p = equivFun (invEquiv (ua a a')) p

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

module _ {A : Type ℓA} {ℓ≅A : Level} (𝒮-A : UARel A ℓ≅A) where
  open UARel 𝒮-A
  J-UARel : {a : A}
            (P : (a' : A) → {p : a ≡ a'} → Type ℓ)
            (d : P a {refl})
            {a' : A}
            (p : a ≅ a')
            → P a' {≅→≡ p}
  J-UARel {a} P d {a'} p
    = J (λ y q → P y {q})
        d
        (≅→≡ p)


Lift-𝒮ᴰ : {A : Type ℓA} (𝒮-A : UARel A ℓ≅A)
        {B : A → Type ℓB}
        {ℓ≅B : Level}
        (𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B)
        {C : A → Type ℓC}
        (𝒮ᴰ-C : DUARel 𝒮-A C ℓ≅C)
        → DUARel (∫ 𝒮ᴰ-C) (λ (a , _) → B a) ℓ≅B
Lift-𝒮ᴰ {A = A} 𝒮-A {B} {ℓ≅B} 𝒮ᴰ-B {C} 𝒮ᴰ-C
  = make-𝒮ᴰ _≅'⟨_⟩_ (λ {(a , c)} b → r {(a , c)} b) cont
  where
    open UARel 𝒮-A renaming (ρ to ρA)
    open DUARel 𝒮ᴰ-B renaming (_≅ᴰ⟨_⟩_ to _≅B⟨_⟩_ ; uaᴰ to uaB ; ρᴰ to ρB)
    open DUARel 𝒮ᴰ-C renaming (_≅ᴰ⟨_⟩_ to _≅C⟨_⟩_ ; uaᴰ to uaC ; ρᴰ to ρC)
    open UARel (∫ 𝒮ᴰ-C) renaming (_≅_ to _≅∫_ ; ua to ua∫ ; ρ to ρ∫)
    _≅'⟨_⟩_ : {(a , c) (a' , c') : Σ A C} → B a → Σ[ p ∈ a ≅ a' ] (c ≅C⟨ p ⟩ c') → B a' → Type ℓ≅B
    b ≅'⟨ p , q ⟩ b' = b ≅B⟨ p ⟩ b'
    r : {(a , c) : Σ A C} → (b : B a) → b ≅'⟨ ρ∫ (a , c) ⟩ b
    -- r : {(a , c) : Σ A C} → (b : B a) → b ≅B⟨ fst (invEq (ua∫ (a , c) (a , c)) refl) ⟩ b
    r {(a , c)} b = subst (λ q → b ≅'⟨ q ⟩ b)
                          (sym (transportRefl (ρA a , ρC c)))
                          (ρB b)
    cont : ((a , c) : Σ A C) → (b : B a) → isContr (Σ[ b' ∈ B a ] (b ≅'⟨ ρ∫ (a , c) ⟩ b'))
    cont (a , c) b = center , k
      where
        center : Σ[ b' ∈ B a ] (b ≅'⟨ ρ∫ (a , c) ⟩ b')
        center = b , r {(a , c)} b
        h : contrRelSingl λ b b' → b ≅B⟨ ρA a ⟩ b'
        h = isUnivalent→contrRelSingl _ uaB
        h' : contrRelSingl λ b b' → b ≅'⟨ ρ∫ (a , c) ⟩ b'
        h' = subst (λ q → contrRelSingl λ b b' → b ≅'⟨ q ⟩ b')
                   (sym (transportRefl (ρA a , ρC c)))
                   h
        g : (b' : B a) → (p : b ≅'⟨ ρ∫ (a , c) ⟩ b') → center ≡ (b' , p)
        g b' p = J (λ w _ → center ≡ w)
                   refl
                   (isContr→isProp (h' b) center (b' , p))
        k : ((b' , p) : Σ[ b' ∈ B a ] (b ≅'⟨ ρ∫ (a , c) ⟩ b')) → center ≡ (b' , p)
        k (b' , p) = g b' p




















{-
-- YET ANOTHER alternative

record DUARel' {A : Type ℓA} {ℓ≅A : Level} (𝒮-A : UARel A ℓ≅A)
              (B : A → Type ℓB) (ℓ≅B : Level) : Type (ℓ-max (ℓ-max ℓA ℓB) (ℓ-max ℓ≅A (ℓ-suc ℓ≅B))) where
  no-eta-equality
  constructor duarel'
  open UARel 𝒮-A

  field
    _≅ᴰ⟨_⟩_ : {a a' : A} → B a → a ≅ a' → B a' → Type ℓ≅B
    uaᴰ : {a : A} → (b b' : B a) → Σ[ p ∈ a ≅ a ] ((b ≅ᴰ⟨ p ⟩ b') ≃ (b ≡ b'))
  ρᴰ : {a : A} → (b : B a) → Σ[ p ∈ a ≅ a ] b ≅ᴰ⟨ p ⟩ b
  ρᴰ {a} b = p , invEq (snd (uaᴰ b b)) refl
    where
      p : a ≅ a
      p = fst (uaᴰ b b)


make-𝒮ᴰ' : {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
           {B : A → Type ℓB}
           (_≅ᴰ⟨_⟩_ : {a a' : A} → B a → UARel._≅_ 𝒮-A a a' → B a' → Type ℓ≅B)
           (uaᴰ : {a : A} → (b b' : B a) → (b ≅ᴰ⟨ UARel.ρ 𝒮-A a ⟩ b') ≃ (b ≡ b'))
          → DUARel' 𝒮-A B ℓ≅B
make-𝒮ᴰ' {𝒮-A = 𝒮-A} _≅ᴰ⟨_⟩_ uaᴰ =  duarel' _≅ᴰ⟨_⟩_ (λ {a} b b' → UARel.ρ 𝒮-A a , uaᴰ b b')

-- temporary:
make-𝒮ᴰ'' : {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
          {B : A → Type ℓB}
          {ℓ≅B : Level}
          (_≅ᴰ⟨_⟩_ : {a a' : A} → B a → UARel._≅_ 𝒮-A a a' → B a' → Type ℓ≅B)
          (ρᴰ : {a : A} → isRefl _≅ᴰ⟨ UARel.ρ 𝒮-A a ⟩_)
          (contrTotal : (a : A) → contrRelSingl _≅ᴰ⟨ UARel.ρ 𝒮-A a ⟩_)
          → DUARel' 𝒮-A B ℓ≅B
make-𝒮ᴰ'' {𝒮-A = 𝒮-A} {B = B} {ℓ≅B = ℓ≅B} _≅ᴰ⟨_⟩_ ρᴰ contrTotal = make-𝒮ᴰ' _≅ᴰ⟨_⟩_ (DUARel.uaᴰ DUA)
  where
  DUA : DUARel 𝒮-A B ℓ≅B
  DUA = make-𝒮ᴰ _≅ᴰ⟨_⟩_ ρᴰ contrTotal
{-
private
  total' : {A : Type ℓA} {ℓ≅A : Level} {𝒮-A : UARel A ℓ≅A}
          {B : A → Type ℓB} {ℓ≅B : Level}
          (𝒮ᴰ-B : DUARel' 𝒮-A B ℓ≅B)
          → UARel (Σ A B) (ℓ-max ℓ≅A ℓ≅B)
  total' {A = A} {ℓ≅A = ℓ≅A} {𝒮-A = 𝒮-A} {B = B} {ℓ≅B = ℓ≅B} 𝒮ᴰ-B =
    make-𝒮 ρΣ c
    where
      open UARel 𝒮-A
      open DUARel' 𝒮ᴰ-B
      _≅Σ_ : Σ A B → Σ A B → Type (ℓ-max ℓ≅A ℓ≅B)
      (a , b) ≅Σ (a' , b') = Σ[ p ∈ a ≅ a' ] (b ≅ᴰ⟨ p ⟩ b')
      ρΣ : isRefl _≅Σ_
      ρΣ (a , b) = ρᴰ b
      c : contrRelSingl _≅Σ_
      c (a , b) = cab , h
        where
          -- cab : relSinglAt _≅Σ_ (a , b)
          cab : Σ[ (a' , b') ∈ Σ A B ] (a , b) ≅Σ (a' , b')
          cab = (a , b) , ρΣ (a , b)
          hB : contrRelSingl (λ b b' → b ≅ᴰ⟨ ρ a ⟩ b')
          hB = {!!}
          g : (b' : B a) (q : b ≅ᴰ⟨ ρ a ⟩ b') → cab ≡ ((a , b') , ρ a , q)
          g b' q = J (λ w _ → cab ≡ ((a , fst w) , ρ a , snd w))
                     {!!}
                     (isContr→isProp (hB b) (b , snd (ρᴰ b)) (b' , q))
          hA : contrRelSingl _≅_
          hA = {!!}
          k : (a' : A) (p : a ≅ a') (b' : B a') (q : b ≅ᴰ⟨ p ⟩ b') → cab ≡ ((a' , b') , (p , q))
          k a' p = J (λ w _ → (b' : B (fst w)) (q : b ≅ᴰ⟨ snd w ⟩ b') → cab ≡ ((fst w , b') , (snd w , q)))
                     g
                     (isContr→isProp (hA a) (a , ρ a) (a' , p))
          h : (y : Σ[ (a' , b') ∈ Σ A B ] (a , b) ≅Σ (a' , b')) → cab ≡ y
          h ((a' , b') , p , q) = k a' p b' q
-}
record DURel {A : Type ℓA} {ℓ≅A : Level} (𝒮-A : UARel A ℓ≅A)
              (B : A → Type ℓB) (ℓ≅B : Level) : Type (ℓ-max (ℓ-max ℓA ℓB) (ℓ-max ℓ≅A (ℓ-suc ℓ≅B))) where
  no-eta-equality
  constructor durel
  open UARel 𝒮-A

  field
    _≅ᴰ⟨_⟩_ : {a a' : A} → B a → a ≅ a' → B a' → Type ℓ≅B
    uaᴰ : {a : A} → (p : a ≅ a) → (b b' : B a) → (b ≅ᴰ⟨ p ⟩ b') ≃ (b ≡ b')
  ρᴰ : {a : A} → (p : a ≅ a) (b : B a) → b ≅ᴰ⟨ p ⟩ b
  ρᴰ {a} p b = invEq (uaᴰ p b b) refl

make-𝒮ᴰ2 : {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
          {B : A → Type ℓB}
          (_≅ᴰ⟨_⟩_ : {a a' : A} → B a → UARel._≅_ 𝒮-A a a' → B a' → Type ℓ≅B)
          (ρᴰ : {a : A} → (p : UARel._≅_ 𝒮-A a a) → isRefl _≅ᴰ⟨ p ⟩_)
          (contrTotal : (a : A) → (p : UARel._≅_ 𝒮-A a a) → contrRelSingl _≅ᴰ⟨ p ⟩_)
          → DURel 𝒮-A B ℓ≅B
DURel._≅ᴰ⟨_⟩_ (make-𝒮ᴰ2 _≅ᴰ⟨_⟩_ ρᴰ contrTotal) = _≅ᴰ⟨_⟩_
DURel.uaᴰ (make-𝒮ᴰ2 {𝒮-A = 𝒮-A} _≅ᴰ⟨_⟩_ ρᴰ contrTotal) {a} p b b'
  = contrRelSingl→isUnivalent (_≅ᴰ⟨ p ⟩_) (ρᴰ p) (contrTotal a p) b b'

private
  total' : {A : Type ℓA} {ℓ≅A : Level} {𝒮-A : UARel A ℓ≅A}
          {B : A → Type ℓB} {ℓ≅B : Level}
          (𝒮ᴰ-B : DURel 𝒮-A B ℓ≅B)
          → UARel (Σ A B) (ℓ-max ℓ≅A ℓ≅B)
  total' {A = A} {ℓ≅A = ℓ≅A} {𝒮-A = 𝒮-A} {B = B} {ℓ≅B = ℓ≅B} 𝒮ᴰ-B
    = make-𝒮 {_≅_ = _≅Σ_} ρΣ c
    where
      open UARel 𝒮-A
      open DURel 𝒮ᴰ-B
      _≅Σ_ : Σ A B → Σ A B → Type (ℓ-max ℓ≅A ℓ≅B)
      (a , b) ≅Σ (a' , b') = Σ[ p ∈ a ≅ a' ] (b ≅ᴰ⟨ p ⟩ b')
      ρΣ : isRefl _≅Σ_
      ρΣ (a , b) = ρ a , ρᴰ (ρ a) b
      c : contrRelSingl _≅Σ_
      c (a , b) = cab , h
        where
          cab : Σ[ (a' , b') ∈ Σ A B ] (a , b) ≅Σ (a' , b')
          cab = (a , b) , ρΣ (a , b)
          hA : contrRelSingl _≅_
          hA = isUnivalent→contrRelSingl _≅_ ua
          hB : contrRelSingl (λ b b' → b ≅ᴰ⟨ ρ a ⟩ b')
          hB = isUnivalent→contrRelSingl (λ b b' → b ≅ᴰ⟨ ρ a ⟩ b') (uaᴰ (ρ a))
          g : (b' : B a) (q : b ≅ᴰ⟨ ρ a ⟩ b') → cab ≡ ((a , b') , ρ a , q)
          g b' q = J (λ w _ → cab ≡ ((a , fst w) , ρ a , snd w))
                     refl (isContr→isProp (hB b) (b , ρᴰ (ρ a) b) (b' , q))
          k : (a' : A) (p : a ≅ a') (b' : B a') (q : b ≅ᴰ⟨ p ⟩ b') → cab ≡ ((a' , b') , (p , q))
          k a' p = J (λ w _ → (b' : B (fst w)) (q : b ≅ᴰ⟨ snd w ⟩ b') → cab ≡ ((fst w , b') , (snd w , q)))
                     g (isContr→isProp (hA a) (a , ρ a) (a' , p))
          h : (y : Σ[ (a' , b') ∈ Σ A B ] (a , b) ≅Σ (a' , b')) → cab ≡ y
          h ((a' , b') , p , q) = k a' p b' q

∫' : {A : Type ℓA} {ℓ≅A : Level} {𝒮-A : UARel A ℓ≅A}
        {B : A → Type ℓB} {ℓ≅B : Level}
        (𝒮ᴰ-B : DURel 𝒮-A B ℓ≅B)
        → UARel (Σ A B) (ℓ-max ℓ≅A ℓ≅B)
UARel._≅_ (∫' 𝒮ᴰ-B) = UARel._≅_ (total' 𝒮ᴰ-B)
UARel.ua (∫' 𝒮ᴰ-B) = UARel.ua (total' 𝒮ᴰ-B)

Lift-𝒮ᴰ : {A : Type ℓA} (𝒮-A : UARel A ℓ≅A)
        {B : A → Type ℓB}
        {ℓ≅B : Level}
        (𝒮ᴰ-B : DURel 𝒮-A B ℓ≅B)
        {C : A → Type ℓC}
        (𝒮ᴰ-C : DURel 𝒮-A C ℓ≅C)
        → DURel (∫' 𝒮ᴰ-C) (λ (a , _) → B a) ℓ≅B
Lift-𝒮ᴰ {A = A} 𝒮-A {B} {ℓ≅B} 𝒮ᴰ-B {C} 𝒮ᴰ-C
  = {!!}
-}

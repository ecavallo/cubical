
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Displayed.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma

open import Cubical.Relation.Binary
open BinaryRelation

open import Cubical.Displayed.Base

private
  variable
    ℓ ℓA ℓA' ℓ≅A ℓB ℓB' ℓ≅B ℓC ℓ≅C : Level

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



splitTotal-𝒮ᴰ : {A : Type ℓA} (𝒮-A : UARel A ℓ≅A)
                {B : A → Type ℓB} {ℓ≅B : Level} (𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B)
                {C : Σ A B → Type ℓC} {ℓ≅C : Level} (𝒮ᴰ-C : DUARel (∫ 𝒮ᴰ-B) C ℓ≅C)
                → DUARel 𝒮-A
                         (λ a → Σ[ b ∈ B a ] C (a , b))
                         (ℓ-max ℓ≅B ℓ≅C)
splitTotal-𝒮ᴰ {A = A} 𝒮-A {B} {ℓ≅B} 𝒮ᴰ-B {C} {ℓ≅C} 𝒮ᴰ-C
  = make-𝒮ᴰ _≅S⟨_⟩_ r cont
  where
    open UARel 𝒮-A renaming (ρ to ρA)
    open DUARel 𝒮ᴰ-B renaming (_≅ᴰ⟨_⟩_ to _≅B⟨_⟩_ ; uaᴰ to uaB ; ρᴰ to ρB)
    open DUARel 𝒮ᴰ-C renaming (_≅ᴰ⟨_⟩_ to _≅C⟨_⟩_ ; uaᴰ to uaC ; ρᴰ to ρC)
    _≅S⟨_⟩_ : {a a' : A}
              → (w : Σ[ b ∈ B a ] C (a , b))
              → (p : a ≅ a')
              → (w' : Σ[ b' ∈ B a' ] C (a' , b'))
              → Type (ℓ-max ℓ≅B ℓ≅C)
    (b , c) ≅S⟨ p ⟩ (b' , c') = Σ[ q ∈ b ≅B⟨ p ⟩ b' ] c ≅C⟨ p , q ⟩ c'
    ρAB : (z : Σ A B) → Σ[ p ∈ (z .fst) ≅ (z .fst)] ((z .snd) ≅B⟨ p ⟩ (z .snd))
    ρAB z = UARel.ρ (∫ 𝒮ᴰ-B) z
    ρABeq : (a : A) (b : B a) → ρAB (a , b) ≡ (ρA a , ρB b)
    ρABeq a b = transportRefl (ρA a , ρB b)
    ρC' : {a : A} {b : B a} (c : C (a , b)) → c ≅C⟨ ρA a , ρB b ⟩ c
    ρC' {a} {b} c = subst (λ q → c ≅C⟨ q ⟩ c) (ρABeq a b) (ρC c)
    r : {a : A} →  isRefl (λ z → _≅S⟨_⟩_ z (ρA a))
    r {a} (b , c) .fst = ρB b
    r {a} (b , c) .snd = ρC' c
    hB : (a : A) → contrRelSingl λ b b' → b ≅B⟨ ρA a ⟩ b'
    hB a = isUnivalent→contrRelSingl _ uaB
    hC : (a : A) (b : B a) → contrRelSingl λ c c' → c ≅C⟨ ρA a , ρB b ⟩ c'
    hC a b = subst (λ q → contrRelSingl λ c c' → c ≅C⟨ q ⟩ c')
                   (ρABeq a b) (isUnivalent→contrRelSingl _ uaC)
    -- cont : (a : A) → contrRelSingl (λ bc → _≅S⟨_⟩_ bc (ρA a))
    cont : (a : A) → (bc : Σ[ b ∈ B a ] C (a , b)) → isContr (Σ[ bc' ∈ (Σ[ b' ∈ B a ] C (a , b')) ] (bc ≅S⟨ ρA a ⟩ bc'))
    cont a (b , c) = center , k
      where
        center : Σ[ bc' ∈ (Σ[ b' ∈ B a ] C (a , b')) ] ((b , c) ≅S⟨ ρA a ⟩ bc')
        center = (b , c) , ρB b , ρC' c
        k : (w : Σ[ bc' ∈ (Σ[ b' ∈ B a ] C (a , b')) ] ((b , c) ≅S⟨ ρA a ⟩ bc')) → center ≡ w
        k ((b' , c') , p , q') = J (λ w _ → (c'' : C (a , w .fst)) (q'' : c ≅C⟨ ρA a , w .snd ⟩  c'')
                                                 → center ≡ ((w .fst , c'') , w .snd , q''))
                                   (λ c'' q'' → J (λ w _ → center ≡ ((b , w .fst) , ρB b , w .snd))
                                      refl (isContr→isProp (hC a b c) (c , ρC' c) (c'' , q'')))
                                   (isContr→isProp (hB a b) (b , ρB b) (b' , p)) c' q'


UARelIso→Iso : {A : Type ℓA} (𝒮-A : UARel A ℓ≅A)
               {B : Type ℓB} (𝒮-B : UARel B ℓ≅B)
               (F : RelIso (UARel._≅_ 𝒮-A) (UARel._≅_ 𝒮-B))
               → Iso A B
UARelIso→Iso 𝒮-A 𝒮-B F
  = RelIso→Iso (UARel._≅_ 𝒮-A)
               (UARel._≅_ 𝒮-B)
               (UARel.≅→≡ 𝒮-A)
               (UARel.≅→≡ 𝒮-B)
               F

DUARel→Π-UARel : {A : Type ℓA} (𝒮-A : UARel A ℓ≅A)
                 {B : A → Type ℓB} (𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B)
                 → UARel ((a : A) → B a) (ℓ-max ℓA ℓ≅B)
DUARel→Π-UARel {ℓA = ℓA} {ℓ≅B = ℓ≅B} {A = A} 𝒮-A {B} 𝒮ᴰ-B
  = uarel _≅Π_ uaΠ
  where
    open UARel 𝒮-A
    open DUARel 𝒮ᴰ-B
    _≅Π_ : (f g : (a : A) → B a) → Type (ℓ-max ℓA ℓ≅B)
    f ≅Π g = (a : A) → f a ≅ᴰ⟨ ρ a ⟩ g a
    uaΠ : (f g : (a : A) → B a) → (f ≅Π g) ≃ (f ≡ g)
    uaΠ f g = ((a : A) → f a ≅ᴰ⟨ ρ a ⟩ g a)
                  ≃⟨ equivΠCod (λ a → uaᴰ (f a) (g a)) ⟩
              ((a : A) → f a ≡ g a)
                  ≃⟨ funExtEquiv ⟩
              f ≡ g ■

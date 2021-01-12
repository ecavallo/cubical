
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Displayed.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Relation.Binary

private
  variable
    ℓA  ℓB : Level


record URel (A : Type ℓA) (ℓ≅A : Level) : Type (ℓ-max ℓA (ℓ-suc ℓ≅A)) where
  no-eta-equality
  constructor urel
  field
    _≅_ : A → A → Type ℓ≅A
    u : {a a' : A} → (a ≅ a') → (a ≡ a')

record DURel {A : Type ℓA} {ℓ≅A : Level} {RA : URel A ℓ≅A}
              (B : A → Type ℓB) (ℓ≅B : Level) : Type (ℓ-max (ℓ-max ℓA ℓB) (ℓ-suc ℓ≅B)) where
  no-eta-equality
  open URel RA

  field
    _D≅_ : {a a' : A} → B a → B a' → Type ℓ≅B
    Du : {a : A} → {b b' : B a} → b D≅ b' → b ≡ b'

∫ : {ℓA  ℓB : Level} {A : Type ℓA} {ℓ≅A : Level} {RA : URel A ℓ≅A}
    {B : A → Type ℓB} {ℓ≅B : Level}
    (RB : DURel {RA = RA} B ℓ≅B)
    → URel (Σ A B) (ℓ-max ℓ≅A ℓ≅B)
URel._≅_ (∫ {RA = RA} RB) (a , b) (a' , b') = a ≅ a' × b D≅ b'
  where
    open URel RA
    open DURel RB
URel.u (∫ {A = A} {RA = RA} {B = B} RB) (pa , pb) = ΣPathP (u pa , duaB pa pb)
  where
    open URel RA
    open DURel RB

    duaB : ∀{a a'} {b : B a} {b' : B a'}
           → (ia : a ≅ a') → b D≅ b' → PathP (λ i → B (u ia i)) b b'
    duaB {a = a} ia ib = J T Du (u ia) ib
      where
        T : (a' : A) → a ≡ a' → Type _
        T a' p = {b : B a} {b' : B a'} → b D≅ b' → PathP (λ i → B (p i)) b b'

{-
total : {A : Type ℓA} {ℓ≅A : Level} {RA : URel A ℓ≅A}
        {B : A → Type ℓB} {ℓ≅B : Level}
        (RB : DURel B ℓ≅B)
        → URel (Σ A B) (ℓ-max ℓ≅A ℓ≅B)
total {A = A} {ℓ≅A = ℓ≅A} {RA = RA} {B = B} {ℓ≅B = ℓ≅B} RB = {!!}
  -- urel _≅Σ_ uaΣ
  where
    open URel RA
    open DURel RB

    _≅Σ_ : Σ A B → Σ A B → Type (ℓ-max ℓ≅A ℓ≅B)
    (a , b) ≅Σ (a' , b') = a ≅ a' × b D≅ b'

    duaB : ∀{a a'} {b : B a} {b' : B a'}
           → (ia : a ≅ a') → b D≅ b' → PathP (λ i → B (u ia i)) b b'
    duaB {a = a} ia ib = J T Du (u ia) ib
      where
        T : (a' : A) → a ≡ a' → Type _
        T a' p = {b : B a} {b' : B a'} → b D≅ b' → PathP (λ i → B (p i)) b b'

    uaΣ : {r r' : Σ A B} → r ≅Σ r' → r ≡ r'
    uaΣ {(a , b)} {(a' , b')} (p₁ , p₂) = ΣPathP (u p₁ , duaB p₁ p₂)
-}
{-
record UARel1 (A : Type ℓA) (ℓ≅A : Level) : Type (ℓ-max ℓA (ℓ-suc ℓ≅A)) where
  no-eta-equality
  constructor uarel1
  field
    _≅_ : A → A → Type ℓ≅A
    ua : {a a' : A} → (a ≅ a') → (a ≡ a')

record DUARel1a {A : Type ℓA} {ℓ≅A : Level} {𝒮-A : UARel1 A ℓ≅A}
              (B : A → Type ℓB) (ℓ≅B : Level) : Type (ℓ-max (ℓ-max ℓA ℓB) (ℓ-suc ℓ≅B)) where
  no-eta-equality
  open UARel1 𝒮-A

  field
    _≅ᴰ_ : {a a' : A} → B a → B a' → Type ℓ≅B
    uaᴰ : {a : A} → {b b' : B a} → b ≅ᴰ b' → b ≡ b'

total1a : {A : Type ℓA} {ℓ≅A : Level} {𝒮-A : UARel1 A ℓ≅A}
          {B : A → Type ℓB} {ℓ≅B : Level}
          (𝒮ᴰ-B : DUARel1a B ℓ≅B)
          → UARel1 (Σ A B) (ℓ-max ℓ≅A ℓ≅B)
total1a {A = A} {ℓ≅A = ℓ≅A} {𝒮-A = 𝒮-A} {B = B} {ℓ≅B = ℓ≅B} 𝒮ᴰ-B =
  uarel1 _≅Σ_ uaΣ
  where
    open UARel1 𝒮-A
    open DUARel1a 𝒮ᴰ-B
    _≅Σ_ : Σ A B → Σ A B → Type (ℓ-max ℓ≅A ℓ≅B)
    (a , b) ≅Σ (a' , b') = a ≅ a' × b ≅ᴰ b'
    duaB : ∀{a a'} {b : B a} {b' : B a'}
           → (ia : a ≅ a') → b ≅ᴰ b' → PathP (λ i → B (ua ia i)) b b'
    duaB {a = a} ia ib = J T uaᴰ (ua ia) ib
      where
        T : (a' : A) → a ≡ a' → Type _
        T a' p = {b : B a} {b' : B a'} → b ≅ᴰ b' → PathP (λ i → B (p i)) b b'
    uaΣ : {r r' : Σ A B} → r ≅Σ r' → r ≡ r'
    uaΣ {(a , b)} {(a' , b')} (p₁ , p₂) = ΣPathP (ua p₁ , duaB p₁ p₂)
-}
{-
record DUARel1b {A : Type ℓA} {ℓ≅A : Level} {𝒮-A : UARel1 A ℓ≅A}
              (B : A → Type ℓB) (ℓ≅B : Level) : Type (ℓ-max (ℓ-max ℓA ℓB) (ℓ-suc ℓ≅B)) where
  no-eta-equality
  open UARel1 𝒮-A
  field
    _≅ᴰ⟨_⟩_ : {a a' : A} → B a → a ≡ a' → B a' → Type ℓ≅B
    uaᴰ : {a : A} → {b b' : B a} → b ≅ᴰ⟨ refl ⟩ b' → b ≡ b'

total1b : {A : Type ℓA} {ℓ≅A : Level} {𝒮-A : UARel1 A ℓ≅A}
          {B : A → Type ℓB} {ℓ≅B : Level}
          (𝒮ᴰ-B : DUARel1b B ℓ≅B)
          → UARel1 (Σ A B) (ℓ-max ℓ≅A ℓ≅B)
total1b {A = A} {ℓ≅A = ℓ≅A} {𝒮-A = 𝒮-A} {B = B} {ℓ≅B = ℓ≅B} 𝒮ᴰ-B =
  uarel1 _≅Σ_ uaΣ
  where
    open UARel1 𝒮-A
    open DUARel1b 𝒮ᴰ-B
    _≅Σ_ : Σ A B → Σ A B → Type (ℓ-max ℓ≅A ℓ≅B)
    (a , b) ≅Σ (a' , b') =  Σ[ p ∈ a ≅ a' ] (b ≅ᴰ⟨ ua p ⟩ b')
    uaΣ : {a a' : Σ A B} → a ≅Σ a' → a ≡ a'
    uaΣ {(a , b)} {(a' , b')} (p₁ , p₂) = ΣPathP (ua p₁ , {!!})

record UARel (A : Type ℓA) (ℓ≅A : Level) : Type (ℓ-max ℓA (ℓ-suc ℓ≅A)) where
  no-eta-equality
  constructor uarel
  field
    _≅_ : A → A → Type ℓ≅A
    ρ : (a : A) → a ≅ a
    ua : {a a' : A} → (a ≅ a') → (a ≡ a')

record DUARel {A : Type ℓA} {ℓ≅A : Level} {𝒮-A : UARel A ℓ≅A}
              (B : A → Type ℓB) (ℓ≅B : Level) : Type (ℓ-max (ℓ-max ℓA ℓB) (ℓ-max ℓ≅A (ℓ-suc ℓ≅B))) where
  no-eta-equality
  constructor duarel
  open UARel 𝒮-A

  field
    _≅ᴰ⟨_⟩_ : {a a' : A} → B a → a ≅ a' → B a' → Type ℓ≅B
    ρᴰ : {a : A} → (b : B a) → b ≅ᴰ⟨ ρ a ⟩ b
    -- uaᴰ : {a : A} → {b b' : B a} → b ≅ᴰ⟨ ρ a ⟩ b' → b ≡ b'
    uaᴰ : {a : A} → {b b' : B a} → b ≅ᴰ⟨ ρ a ⟩ b' → PathP (λ i → B (ua (ρ a) i)) b b'

total : {A : Type ℓA} {ℓ≅A : Level} {𝒮-A : UARel A ℓ≅A}
        {B : A → Type ℓB} {ℓ≅B : Level}
        (𝒮ᴰ-B : DUARel B ℓ≅B)
        → UARel (Σ A B) (ℓ-max ℓ≅A ℓ≅B)
total {A = A} {ℓ≅A = ℓ≅A} {𝒮-A = 𝒮-A} {B = B} {ℓ≅B = ℓ≅B} 𝒮ᴰ-B =
  uarel _≅Σ_ ρΣ uaΣ
  where
    open UARel 𝒮-A
    open DUARel 𝒮ᴰ-B
    _≅Σ_ : Σ A B → Σ A B → Type (ℓ-max ℓ≅A ℓ≅B)
    (a , b) ≅Σ (a' , b') = Σ[ p ∈ a ≅ a' ] (b ≅ᴰ⟨ p ⟩ b')
    ρΣ : (r : Σ A B) → r ≅Σ r
    ρΣ (a , b) = ρ a , ρᴰ b
    uaΣ : {r r' : Σ A B} → r ≅Σ r' → r ≡ r'
    uaΣ {r} {r'} (p₁ , p₂) = ΣPathP (ua p₁ , uaᴰ {!!})
-}
{-
module Total {A : Type u} {B : A → Type u'} (AR : URel A t) (BR : DURel B t') where
  open URel AR renaming (_≅_ to _≅A_; ua to uaA)
  open DURel BR renaming (_≅_ to _≅B_; ua to uaB)

  duaB : ∀{a a'} {b : B a} {b' : B a'}
       → (ia : a ≅A a') → b ≅B b' → PathP (λ i → B (uaA ia i)) b b'
  duaB {a = a} ia ib = J T uaB (uaA ia) ib
    where
    T : (a' : A) → a ≡ a' → Type _
    T a' p = {b : B a} {b' : B a'} → b ≅B b' → PathP (λ i → B (p i)) b b'

  _≅Σ_ : Σ A B → Σ A B → Type _
  (x , y) ≅Σ (x' , y') = (x ≅A x') × (y ≅B y')

  uaΣ : (p q : Σ A B) → p ≅Σ q → p ≡ q
  uaΣ (x , y) (x' , y') (x≅x' , y≅y') = ΣPathP (uaA x≅x' , duaB x≅x' y≅y')
-}

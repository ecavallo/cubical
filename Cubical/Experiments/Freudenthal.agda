{-# OPTIONS --cubical --safe #-}
module Cubical.Experiments.Freudenthal where

open import Cubical.Foundations.Everything
open import Cubical.Data.HomotopyGroup
open import Cubical.Data.Nat
import Cubical.Data.NatMinusTwo as ℕ₋₂
open import Cubical.Data.Sigma
open import Cubical.HITs.Nullification
open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation as Trunc

-- To be moved elsewhere

flipSquare : ∀ {ℓ} {A : Type ℓ}
  {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁}
  {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
  {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁}
  → Square a₀₋ a₁₋ a₋₀ a₋₁
  → Square a₋₀ a₋₁ a₀₋ a₁₋
flipSquare sq i j = sq j i

flipSquarePath : ∀ {ℓ} {A : Type ℓ}
  {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁}
  {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
  {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁}
  → Square a₀₋ a₁₋ a₋₀ a₋₁ ≡ Square a₋₀ a₋₁ a₀₋ a₁₋
flipSquarePath = isoToPath (iso flipSquare flipSquare (λ _ → refl) (λ _ → refl))

fiber≡ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B} {b : B} (h h' : fiber f b)
  → (h ≡ h') ≡ fiber (cong f) (h .snd ∙∙ refl ∙∙ sym (h' .snd))
fiber≡ {f = f} h h' =
  ua Σ≡ ⁻¹ ∙
  cong (Σ (h .fst ≡ h' .fst)) (funExt λ p → flipSquarePath ∙ PathP≡doubleCompPathʳ _ _ _ _)

isOfHLevelMap : ∀ {ℓ ℓ'} (n : ℕ) {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type (ℓ-max ℓ ℓ')
isOfHLevelMap n f = ∀ b → isOfHLevel n (fiber f b)

∙Susp : ∀ {ℓ} (A : Type ℓ) → Pointed ℓ
∙Susp A = Susp A , north

-- connectedness

isHLevelConnected : ∀ {ℓ} (n : ℕ) (A : Type ℓ) → Type ℓ
isHLevelConnected n A = isContr (hLevelTrunc n A)

isHLevelConnectedMap : ∀ {ℓ ℓ'} (n : ℕ) {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type (ℓ-max ℓ ℓ')
isHLevelConnectedMap n f = ∀ b → isHLevelConnected n (fiber f b)

isEquivPrecomposeConnected : ∀ {ℓ ℓ' ℓ''} (n : ℕ)
  {A : Type ℓ} {B : Type ℓ'} (P : B → HLevel ℓ'' n) (f : A → B)
  → isHLevelConnectedMap n f
  → isEquiv (λ(s : (b : B) → P b .fst) → s ∘ f)
isEquivPrecomposeConnected n {A} {B} P f fConn =
  isoToIsEquiv
    (iso (_∘ f)
      (λ t b → inv t b (fConn b .fst))
      (λ t → funExt λ a →
        cong (inv t (f a)) (fConn (f a) .snd ∣ a , refl ∣)
        ∙ substRefl {B = fst ∘ P} (t a))
      (λ s → funExt λ b →
        Trunc.elim
          {B = λ d → inv (s ∘ f) b d ≡ s b}
          (λ _ → isOfHLevelPath n (P b .snd) _ _)
          (λ {(a , p) i → transp (λ j → P (p (j ∨ i)) .fst) i (s (p i))})
          (fConn b .fst)))
  where
  inv : ((a : A) → P (f a) .fst) → (b : B) → hLevelTrunc n (fiber f b) → P b .fst
  inv t b =
    Trunc.rec
      (P b .snd)
      (λ {(a , p) → subst (fst ∘ P) p (t a)})

isOfHLevelPrecomposeConnected : ∀ {ℓ ℓ' ℓ''} (k : ℕ) (n : ℕ)
  {A : Type ℓ} {B : Type ℓ'} (P : B → HLevel ℓ'' (k + n)) (f : A → B)
  → isHLevelConnectedMap n f
  → isOfHLevelMap k (λ(s : (b : B) → P b .fst) → s ∘ f)
isOfHLevelPrecomposeConnected zero n P f fConn =
  isEquivPrecomposeConnected n P f fConn .equiv-proof
isOfHLevelPrecomposeConnected (suc k) n P f fConn t =
    isOfHLevelPath'⁻ k
      (λ {(s₀ , p₀) (s₁ , p₁) →
        subst (isOfHLevel k) (sym (fiber≡ (s₀ , p₀) (s₁ , p₁)))
          (isOfHLevelRetract k
            (λ {(q , α) → (funExt⁻ q) , (cong funExt⁻ α)})
            (λ {(h , β) → (funExt h) , (cong funExt β)})
            (λ _ → refl)
            (isOfHLevelPrecomposeConnected k n
              (λ b → (s₀ b ≡ s₁ b) , isOfHLevelPath' (k + n) (P b .snd) _ _)
              f fConn
              (funExt⁻ (p₀ ∙∙ refl ∙∙ sym p₁))))})

isHLevelConnectedPath : ∀ {ℓ} (n : ℕ) {A : Type ℓ}
  → isHLevelConnected (suc n) A
  → (a₀ a₁ : A) → isHLevelConnected n (a₀ ≡ a₁)
isHLevelConnectedPath n connA a₀ a₁ =
  subst isContr (PathIdTrunc (ℕ₋₂.-2+ n))
    (isContr→isContrPath connA _ _)

isHLevelConnectedRetract : ∀ {ℓ ℓ'} (n : ℕ)
  {A : Type ℓ} {B : Type ℓ'}
  (f : A → B) (g : B → A)
  (h : (x : A) → g (f x) ≡ x)
  → isHLevelConnected n B → isHLevelConnected n A
isHLevelConnectedRetract n f g h =
  isContrRetract
    (Trunc.map f)
    (Trunc.map g)
    (Trunc.elim
      (λ _ → isOfHLevelPath n (isOfHLevelTrunc n) _ _)
      (λ a → cong ∣_∣ (h a)))

isHLevelConnectedPoint : ∀ {ℓ} (n : ℕ) {A : Type ℓ}
  → isHLevelConnected (suc n) A
  → (a : A) → isHLevelConnectedMap n (λ(_ : Unit) → a)
isHLevelConnectedPoint n connA a₀ a =
  isHLevelConnectedRetract n
    snd (_ ,_) (λ _ → refl)
    (isHLevelConnectedPath n connA a₀ a)

-- wedge connectivity

module WedgeConnectivity {ℓ ℓ' ℓ''} (n m : ℕ)
  (A : Pointed ℓ) (connA : isHLevelConnected (suc n) (typ A))
  (B : Pointed ℓ') (connB : isHLevelConnected (suc m) (typ B))
  (P : typ A → typ B → HLevel ℓ'' (n + m))
  (f : (a : typ A) → P a (pt B) .fst)
  (g : (b : typ B) → P (pt A) b .fst)
  (p : f (pt A) ≡ g (pt B))
  where

  private
    Q : typ A → HLevel _ n
    Q a =
      ( (Σ[ k ∈ ((b : typ B) → P a b .fst) ] k (pt B) ≡ f a)
      , isOfHLevelRetract n
          (λ {(h , q) → h , funExt λ _ → q})
          (λ {(h , q) → h , funExt⁻ q _})
          (λ _ → refl)
          (isOfHLevelPrecomposeConnected n m (P a) (λ _ → pt B)
            (isHLevelConnectedPoint m connB (pt B)) (λ _ → f a))
      )

    main : isContr (fiber (λ s _ → s (pt A)) (λ _ → g , p ⁻¹))
    main =
      isEquivPrecomposeConnected n Q (λ _ → pt A)
        (isHLevelConnectedPoint n connA (pt A))
        .equiv-proof (λ _ → g , p ⁻¹)

  extension : ∀ a b → P a b .fst
  extension a b = main .fst .fst a .fst b

  left : ∀ a → extension a (pt B) ≡ f a
  left a = main .fst .fst a .snd

  right : ∀ b → extension (pt A) b ≡ g b
  right = funExt⁻ (cong fst (funExt⁻ (main .fst .snd) _))

-- freudenthal (partial)

module Freudenthal {ℓ} (n : ℕ)
  {A : Pointed ℓ} (connA : isHLevelConnected (suc (suc n)) (typ A))
  where

  private
    2n+2 = suc n + suc n

  σ : typ A → typ (Ω (∙Susp (typ A)))
  σ a = merid a ∙ merid (pt A) ⁻¹

  Code : (y : Susp (typ A)) → north ≡ y → Type ℓ
  Code north p = hLevelTrunc 2n+2 (fiber σ p)
  Code south q = hLevelTrunc 2n+2 (fiber merid q)
  Code (merid a i) p =
    Glue
      (hLevelTrunc 2n+2
        (fiber (λ x j → compPath-filler (merid x) (merid a ⁻¹) (~ i) j) p))
      (λ
        { (i = i0) → _ , (fwd p a , isEquivFwd p a)
        ; (i = i1) → _ , idEquiv _
        })
    where
    module WC (p : north ≡ north) =
      WedgeConnectivity (suc n) (suc n) A connA A connA
        (λ a b →
          ( (σ b ≡ p → hLevelTrunc 2n+2 (fiber (λ x → merid x ∙ merid a ⁻¹) p))
          , isOfHLevelPi 2n+2 λ _ → isOfHLevelTrunc 2n+2
          ))
        (λ a r → ∣ a , (rCancel (merid a) ∙ rCancel (merid (pt A)) ⁻¹) ∙ r ∣)
        (λ b r → ∣ b , r ∣)
        (funExt λ r →
          cong ∣_∣
            (cong (pt A ,_)
              (cong (_∙ r) (rCancel (rCancel (merid (pt A)))) ∙ lUnit r ⁻¹)))
      
    fwd : (p : north ≡ north) (a : typ A) 
      → hLevelTrunc 2n+2 (fiber σ p)
      → hLevelTrunc 2n+2 (fiber (λ x → merid x ∙ merid a ⁻¹) p)
    fwd p a = Trunc.rec (isOfHLevelTrunc 2n+2) (uncurry (WC.extension p a))

    isEquivFwd : (p : north ≡ north) (a : typ A) → isEquiv (fwd p a)
    isEquivFwd p a .equiv-proof =
      isEquivPrecomposeConnected (suc n)
        (λ a →
          ( (∀ t → isContr (fiber (fwd p a) t))
          , isProp→isOfHLevelSuc n (isPropPi λ _ → isPropIsContr)
          ))
        (λ _ → pt A)
        (isHLevelConnectedPoint (suc n) connA (pt A))
        .equiv-proof
        (λ _ → Trunc.elim
          (λ _ → isProp→isOfHLevelSuc (n + suc n) isPropIsContr)
          (λ fib →
            subst (λ k → isContr (fiber k ∣ fib ∣))
              (cong (Trunc.rec (isOfHLevelTrunc 2n+2) ∘ uncurry)
                (funExt (WC.right p) ⁻¹))
              (subst isEquiv
                (funExt (Trunc.mapId) ⁻¹)
                (idIsEquiv _)
                .equiv-proof ∣ fib ∣)
            ))
        .fst .fst a

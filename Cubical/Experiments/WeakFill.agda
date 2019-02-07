{-# OPTIONS --cubical #-}
module Cubical.Experiments.WeakFill where

open import Cubical.Core.Everything
open import Agda.Builtin.Cubical.Glue renaming (primFaceForall to ∀I)

-- postulate weak com
module _ {ℓ} (A : ∀ i → Set ℓ) {φ : I} (u : ∀ i → Partial φ (A i)) (i : I) (ui : A i [ φ ↦ u i ]) where
  postulate
    wcom : (j : I) → A j [ φ ↦ u j ]
    wcap : (ouc (wcom i) ≡ ouc ui) [ φ ↦ (λ {(φ = i1) → refl}) ]

-- derive homogeneous com
module _ {ℓ} (A : Set ℓ) {φ : I} (u : ∀ i → Partial φ A) (i : I) (ui : A [ φ ↦ u i ]) where

  whcom : (j : I) → A [ φ ↦ u j ]
  whcom = wcom (λ _ → A) u i ui

  whcap : (ouc (whcom i) ≡ ouc ui) [ φ ↦ (λ {(φ = i1) → refl}) ]
  whcap = wcap (λ _ → A) u i ui

-- derive coercion
module _ {ℓ} (A : ∀ i → Set ℓ) (i : I) (ui : A i)  where

  wccom : (j : I) → A j
  wccom j = ouc (wcom A {i0} (λ _ ()) i (inc ui) j)

  wccap : wccom i ≡ ui
  wccap = ouc (wcap A {i0} (λ _ ()) i (inc ui))

-- derive strict com to and from 0 or 1
-- The general principle is that strict com r->s is derivable when r = s is a cofibration.

module _ {ℓ} (A : ∀ i → Set ℓ) {φ : I} (u : ∀ i → Partial φ (A i)) (u0 : A i0 [ φ ↦ u i0 ]) where

  scom0→ : (j : I) → A j [ φ ↦ u j ]
  scom0→ j =
    inc (ouc (whcom (A j) {φ ∨ ~ j}
      (λ k → λ
        { (φ = i1) → u j 1=1
        ; (j = i0) → ouc (wcap A u i0 u0) k
        })
      i0
      (inc (ouc (wcom A u i0 u0 j)))
      i1))

module _ {ℓ} (A : ∀ i → Set ℓ) {φ : I} (u : ∀ i → Partial φ (A i)) (u1 : A i1 [ φ ↦ u i1 ]) where

  scom1→ : (j : I) → A j [ φ ↦ u j ]
  scom1→ j =
    inc (ouc (whcom (A j) {φ ∨ j}
      (λ k → λ
        { (φ = i1) → u j 1=1
        ; (j = i1) → ouc (wcap A u i1 u1) k
        })
      i0
      (inc (ouc (wcom A u i1 u1 j)))
      i1))

module _ {ℓ} (A : ∀ i → Set ℓ) {φ : I} (u : ∀ i → Partial φ (A i)) (i : I) (ui : A i [ φ ↦ u i ]) where

  scom→0 : A i0 [ φ ↦ u i0 ]
  scom→0 =
    inc (ouc (whcom (A i0) {φ ∨ ~ i}
      (λ k → λ
        { (φ = i1) → u i0 1=1
        ; (i = i0) → ouc (wcap A u i ui) k
        })
      i0
      (inc (ouc (wcom A u i ui i0)))
      i1))

  scom→1 : A i1 [ φ ↦ u i1 ]
  scom→1 =
    inc (ouc (whcom (A i1) {φ ∨ i}
      (λ k → λ
        { (φ = i1) → u i1 1=1
        ; (i = i1) → ouc (wcap A u i ui) k
        })
      i0
      (inc (ouc (wcom A u i ui i1)))
      i1))

-- demonstrate that type formers support wcom+wcap structures

module Sigma {ℓ} (A : ∀ i → Set ℓ) (B : ∀ i → A i → Set ℓ)
  {φ : I}
  (u : ∀ i → Partial φ (Σ[ a ∈ A i ] (B i a)))
  (i : I)
  (ui : (Σ[ a ∈ A i ] (B i a)) [ φ ↦ u i ])
  where

  private
    -- first component
    uA : ∀ i → Partial φ (A i)
    uA i w = fst (u i w)

    uiA : A i [ φ ↦ uA i ]
    uiA = inc (fst (ouc ui))

    comA : (j : I) → A j [ φ ↦ uA j ]
    comA = wcom A uA i uiA

    capA : (ouc (comA i) ≡ ouc uiA) [ φ ↦ (λ {(φ = i1) → refl}) ]
    capA = wcap A uA i uiA

    -- second component
    uB : ∀ i → Partial φ (B i (ouc (comA i)))
    uB i = λ {(φ = i1) → snd (u i 1=1)}

    uiB1 : B i (ouc uiA) [ φ ↦ (λ {(φ = i1) → uB i 1=1}) ]
    uiB1 = inc (snd (ouc ui))

    -- need to adjust type of uiB1 by capA
    uiB : ∀ k → B i (ouc capA k) [ φ ↦ (λ {(φ = i1) → uB i 1=1}) ]
    uiB k = scom1→ (λ k → B i (ouc capA k)) (λ _ → λ {(φ = i1) → uB i 1=1}) uiB1 k

    comB : (j : I) → B j (ouc (comA j)) [ φ ↦ uB j ]
    comB = wcom (λ k → B k (ouc (comA k))) uB i (uiB i0)

  sigma-wcom : (j : I) → (Σ[ a ∈ A j ] (B j a)) [ φ ↦ u j ]
  sigma-wcom j = inc (ouc (comA j), ouc (comB j))

  private
    capB0 : (ouc (comB i) ≡ ouc (uiB i0)) [ φ ↦ (λ {(φ = i1) → refl}) ]
    capB0 = wcap (λ j → B j (ouc (comA j))) uB i (uiB i0)

    capB1 : ∀ l → B i (ouc capA l)
    capB1 l = ouc
      (whcom (B i (ouc capA l))
        (λ m → λ
          { (l = i0) → ouc capB0 m
          ; (l = i1) → ouc uiB1
          ; (φ = i1) → uB i 1=1
          })
        i1
        (inc (ouc (uiB l)))
        i0)

  sigma-wcap : (ouc (sigma-wcom i) ≡ ouc ui) [ φ ↦ (λ {(φ = i1) → refl}) ]
  sigma-wcap = inc (λ l → ouc capA l , capB1 l)

module Pi {ℓ} (A : ∀ i → Set ℓ) (B : ∀ i → A i → Set ℓ)
  {φ : I}
  (u : ∀ i → Partial φ ((a : A i) → (B i a)))
  (i : I)
  (ui : ((a : A i) → B i a) [ φ ↦ u i ])
  where

  private
    module PiHelp (j : I) (aj : A j) where
      a : (i : I) → A i
      a i = wccom A j aj i

      acap : a j ≡ aj
      acap = wccap A j aj

      comB : B j (a j) [ φ ↦ (λ v → u j v (a j)) ]
      comB = wcom (λ i → B i (a i)) (λ i v → u i v (a i)) i (inc (ouc ui (a i))) j

      fixcom : ∀ k → B j (acap k) [ φ ↦ (λ v → u j v (acap k)) ] → B j aj [ φ ↦ (λ v → u j v aj) ]
      fixcom k b = scom→1 (λ k → B j (acap k)) (λ k → λ {(φ = i1) → u j 1=1 (acap k)}) k b

      fix = fixcom i0

  pi-wcom : (j : I) → ((a : A j) → B j a) [ φ ↦ u j ]
  pi-wcom j = inc (λ aj → let open PiHelp j aj in ouc (fix comB))

  private
    module _ (ai : A i) where
      open PiHelp i ai

      capB : (ouc comB ≡ ouc ui (a i)) [ φ ↦ (λ {(φ = i1) → refl}) ]
      capB = wcap (λ i → B i (a i)) (λ i v → u i v (a i)) i (inc (ouc ui (a i)))

      capB-fix : ouc (fix comB) ≡ ouc ui ai
      capB-fix k = ouc
        (whcom (B i ai)
          (λ m → λ
            { (k = i0) → ouc (fix (inc (ouc capB m)))
            ; (k = i1) → ouc ui ai
            ; (φ = i1) → u i 1=1 ai
            })
          i1
          (inc (ouc (fixcom k (inc (ouc ui (acap k))))))
          i0)

  pi-wcap : (ouc (pi-wcom i) ≡ ouc ui) [ φ ↦ (λ {(φ = i1) → refl}) ]
  pi-wcap = inc (λ k ai → capB-fix ai k)

module Path {ℓ} (A : ∀ i → I → Set ℓ) (a0 : ∀ i → A i i0) (a1 : ∀ i → A i i1)
  {φ : I}
  (u : ∀ i → Partial φ (PathP (A i) (a0 i) (a1 i)))
  (i : I)
  (ui : (PathP (A i) (a0 i) (a1 i)) [ φ ↦ u i ])
  where

  path-wcom : (j : I) → (PathP (A j) (a0 j) (a1 j)) [ φ ↦ u j ]
  path-wcom j = inc (λ t → ouc
    (wcom (λ i → A i t)
      (λ k → λ {(φ = i1) → u k 1=1 t; (t = i0) → a0 k; (t = i1) → a1 k})
      i
      (inc (ouc ui t))
      j)
    )

  path-wcap : (ouc (path-wcom i) ≡ ouc ui) [ φ ↦ (λ {(φ = i1) → refl}) ]
  path-wcap = inc (λ k t → ouc
    (wcap (λ i → A i t)
      (λ k → λ {(φ = i1) → u k 1=1 t; (t = i0) → a0 k; (t = i1) → a1 k})
      i
      (inc (ouc ui t)))
    k)

-- This covers the case where the cofibration of the Glue type does not vary in the direction of composition.
-- We cannot formalize the general case because of the limitations of cubical Agda, but I have tried to write
-- the code in a way that easily generalizes (using ∀I where it would be necessary in the general case).
module SomeGlue {ℓ} (A : I → Set ℓ) (φ : I)
  (P : (i : I) → Partial φ (Σ[ T ∈ Set ℓ ] (T ≃ A i)))
  {ψ : I}
  (u : ∀ i → Partial ψ (Glue (A i) (P i)))
  (i : I)
  (ui : (Glue (A i) (P i)) [ ψ ↦ u i ])
  where

  private
    T : (i : I) → Partial φ (Set ℓ)
    T i v = fst (P i v)

    e : (i : I) → PartialP φ (λ v → T i v ≃ A i)
    e i v = snd (P i v)

    a : ∀ i → Partial ψ (A i)
    a i v = unglue φ (u i v)

    a₀ : A i [ ψ ↦ a i ]
    a₀ = inc (unglue φ (ouc ui))

    b̃ : ∀ j → PartialP (∀I (λ _ → φ)) (λ v → T j v)
    b̃ j = λ {(∀I (λ _ → φ) = i1) → ouc (wcom (λ j → T j 1=1) u i ui j)}

    b̃-cap : PartialP {ℓ} (∀I (λ _ → φ)) (λ {(∀I (λ _ → φ) = i1) → b̃ i 1=1 ≡ ouc ui})
    b̃-cap = λ {(∀I (λ _ → φ) = i1) → ouc (wcap (λ j → T j 1=1) u i ui)}

    a₀-fix : I → A i
    a₀-fix k = ouc
      (scom1→ (λ _ → A i) {ψ ∨ ∀I (λ _ → φ)}
        (λ k → λ
          { (ψ = i1) → a i 1=1
          ; (∀I (λ _ → φ) = i1) → e i 1=1 .fst (b̃-cap 1=1 k)
          })
          (inc (ouc a₀))
          k)

    a₁ : ∀ j → A j
    a₁ j = ouc
      (wcom A {ψ ∨ ∀I (λ i → φ)}
        (λ j → λ
          { (ψ = i1) → a j 1=1
          ; (∀I (λ _ → φ) = i1) → e j 1=1 .fst (b̃ j 1=1)
          })
        i
        (inc (a₀-fix i0))
        j)

    C₁ : ∀ j → PartialP φ (λ v → fiber (e j v .fst) (a₁ j))
    C₁ j = λ {(φ = i1) → e j 1=1 .snd .equiv-proof (a₁ j) .fst}

    C₂ : ∀ j → PartialP φ (λ v → (f : fiber (e j v .fst) (a₁ j)) → C₁ j v ≡ f)
    C₂ j = λ {(φ = i1) → e j 1=1 .snd .equiv-proof (a₁ j) .snd}

    R : ∀ j → PartialP φ (λ v → fiber (e j v .fst) (a₁ j))
    R j = λ {(φ = i1) → ouc
      (scom0→ (λ _ → fiber (e j 1=1 .fst) (a₁ j))
        (λ m → λ
          { (ψ = i1) → C₂ j 1=1 (u j 1=1 , refl) m
          ; (∀I (λ _ → φ) = i1) → C₂ j 1=1 (b̃ j 1=1 , refl) m
          })
        (inc (C₁ j 1=1))
        i1)}

    a₁' : ∀ j → A j
    a₁' j = ouc
      (scom1→ (λ _ → A j)
        (λ m → λ
          { (ψ = i1) → a j 1=1
          ; (φ = i1) → R j 1=1 .snd m
          })
        (inc (a₁ j))
        i0)

  glue-wcom : (j : I) → (Glue (A j) (P j)) [ ψ ↦ u j ]
  glue-wcom j = inc (glue (λ v → R j v .fst) (a₁' j))

  -- check coherence
  _ : (j : I) → PartialP {ℓ} φ (λ {(φ = i1) → ouc (glue-wcom j) ≡ ouc (wcom (λ i → T i 1=1) u i ui j)})
  _ = λ j → λ {(φ = i1) → refl}

  private
    a₁-step : a₁ i ≡ a₀-fix i0
    a₁-step = ouc
      (wcap A {ψ ∨ ∀I (λ i → φ)}
        (λ j → λ
          { (ψ = i1) → a j 1=1
          ; (∀I (λ _ → φ) = i1) → e j 1=1 .fst (b̃ j 1=1)
          })
        i
        (inc (a₀-fix i0)))

    a₁-cap : a₁ i ≡ ouc a₀
    a₁-cap k = ouc
      (scom1→ (λ _ → A i)
        (λ m → λ
          { (ψ = i1) → a₁ i
          ; (∀I (λ _ → φ) = i1) → e i 1=1 .fst (b̃-cap 1=1 k)
          ; (k = i0) → a₁-step m
          ; (k = i1) → ouc a₀
          })
        (inc (a₀-fix k))
        i0)

    C₁-cap : ∀ k → PartialP φ (λ v → fiber (e i v .fst) (a₁-cap k))
    C₁-cap k = λ {(φ = i1) → e i 1=1 .snd .equiv-proof (a₁-cap k) .fst}

    C₂-cap : ∀ k → PartialP φ (λ v → (f : fiber (e i v .fst) (a₁-cap k)) → C₁-cap k v ≡ f)
    C₂-cap k = λ {(φ = i1) → e i 1=1 .snd .equiv-proof (a₁-cap k) .snd}

    R-cap : ∀ k → PartialP {ℓ} φ (λ v → fiber (e i v .fst) (a₁-cap k))
    R-cap k = λ {(φ = i1) → ouc
      (scom0→ (λ _ → fiber (e i 1=1 .fst) (a₁-cap k))
        (λ m → λ
          { (ψ = i1) → C₂-cap k 1=1 (u i 1=1 , refl) m
          ; (∀I (λ _ → φ) = i1) → C₂-cap k 1=1 (b̃-cap 1=1 k , refl) m
          ; (k = i1) → C₂-cap k 1=1 (ouc ui , refl) m
          })
        (inc (C₁-cap k 1=1))
        i1)}

    a₁'-cap : I → A i
    a₁'-cap k = ouc
      (scom1→ (λ _ → A i)
        (λ m → λ
          { (ψ = i1) → a i 1=1
          ; (φ = i1) → R-cap k 1=1 .snd m
          ; (k = i1) → ouc a₀
          })
        (inc (a₁-cap k))
        i0)

  glue-wcap : (ouc (glue-wcom i) ≡ ouc ui) [ ψ ↦ (λ {(ψ = i1) → refl}) ]
  glue-wcap = inc (λ k → glue (λ v → R-cap k v .fst) (a₁'-cap k))

  -- check coherence
  _ : PartialP {ℓ} φ (λ {(φ = i1) → ouc glue-wcap ≡ ouc (wcap (λ i → T i 1=1) u i ui)})
  _ = λ {(φ = i1) → refl}

-- com from homogeneous com and coercion, necessary for higher inductive types
module Recompose {ℓ} (A : ∀ i → Set ℓ)
  {φ : I}
  (u : ∀ i → Partial φ (A i))
  (i : I)
  (ui : A i [ φ ↦ u i ])
  where

  private
    step0 : (j : I) → A j [ φ ↦ (λ {(φ = i1) → wccom A j (u j 1=1) j}) ]
    step0 j =
      whcom (A j) (λ k v → wccom A k (u k v) j) i (inc (wccom A i (ouc ui) j)) j

  wcom' : (j : I) → A j [ φ ↦ u j ]
  wcom' j =
    whcom (A j) (λ k → λ {(φ = i1) → wccap A j (u j 1=1) k}) i0 (step0 j) i1

  private
    step0-cap : (ouc (step0 i) ≡ wccom A i (ouc ui) i) [ φ ↦ (λ {(φ = i1) → refl}) ]
    step0-cap =
      whcap (A i) (λ k v → wccom A k (u k v) i) i (inc (wccom A i (ouc ui) i))

    step1 : (k : I) → A i
    step1 k = ouc
      (whcom (A i)
        (λ m → λ
          { (k = i0) → ouc (wcom' i)
          ; (k = i1) →
            ouc (whcom (A i) (λ k v → wccap A i (u i v) k) m (inc (wccap A i (ouc ui) m)) i1)
          ; (φ = i1) → u i 1=1
          })
        i0
        (inc (ouc (whcom (A i) (λ k v → wccap A i (u i v) k) i0 (inc (ouc step0-cap k)) i1)))
        i1)

  wcap' : (ouc (wcom' i) ≡ ouc ui) [ φ ↦ (λ {(φ = i1) → refl}) ]
  wcap' = inc (λ k → ouc
    (whcom (A i)
      (λ m → λ
        { (k = i0) → ouc (wcom' i)
        ; (k = i1) → ouc (whcap (A i) (λ k v → wccap A i (u i v) k) i1 ui) m
        ; (φ = i1) → u i 1=1
        })
      i0
      (inc (step1 k))
      i1))

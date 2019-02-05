{-# OPTIONS --cubical #-}
module Cubical.Experiments.WeakFill where

open import Cubical.Core.Everything

postulate
  wfill : ∀ {ℓ} (A : ∀ i → Set ℓ)
         {φ : I}
         (u : ∀ i → Partial φ (A i))
         (i : I)
         (ui : A i [ φ ↦ u i ])
         ---------------------------
         (j : I) → A j [ φ ↦ u j ]

  wcap : ∀ {ℓ} (A : ∀ i → Set ℓ)
         {φ : I}
         (u : ∀ i → Partial φ (A i))
         (i : I)
         (ui : A i [ φ ↦ u i ])
         ---------------------------
         → (ouc (wfill A u i ui i) ≡ ouc ui) [ φ ↦ (λ {(φ = i1) → refl}) ]

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

    fillA : (j : I) → A j [ φ ↦ uA j ]
    fillA = wfill A uA i uiA

    capA : (ouc (fillA i) ≡ ouc uiA) [ φ ↦ (λ {(φ = i1) → refl}) ]
    capA = wcap A uA i uiA

    -- second component
    uB : ∀ i → Partial φ (B i (ouc (fillA i)))
    uB i = λ {(φ = i1) → snd (u i 1=1)}

    uiB1 : B i (ouc uiA) [ φ ↦ (λ {(φ = i1) → uB i 1=1}) ]
    uiB1 = inc (snd (ouc ui))

    -- need to adjust type of uiB1 by capA
    uiBfill : ∀ k → B i (ouc capA k) [ φ ↦ (λ {(φ = i1) → uB i 1=1}) ]
    uiBfill k = wfill (λ k → B i (ouc capA k)) (λ _ → λ {(φ = i1) → uB i 1=1}) i1 uiB1 k

    uiB0 : B i (ouc (fillA i)) [ φ ↦ uB i ]
    uiB0 = uiBfill i0

    fillB : (j : I) → B j (ouc (fillA j)) [ φ ↦ uB j ]
    fillB = wfill (λ k → B k (ouc (fillA k))) uB i uiB0 

  sigma-wfill : (j : I) → (Σ[ a ∈ A j ] (B j a)) [ φ ↦ u j ]
  sigma-wfill j = inc (ouc (fillA j), ouc (fillB j))

  private
    uiBcap : (ouc (uiBfill i1) ≡ ouc uiB1) [ φ ↦ (λ {(φ = i1) → refl}) ]
    uiBcap = wcap (λ k → B i (ouc capA k)) (λ _ → λ {(φ = i1) → uB i 1=1}) i1 uiB1

    capB : (ouc (fillB i) ≡ ouc uiB0) [ φ ↦ (λ {(φ = i1) → refl}) ]
    capB = wcap (λ j → B j (ouc (fillA j))) uB i uiB0

  sigma-wcap : (ouc (sigma-wfill i) ≡ ouc ui) [ φ ↦ (λ {(φ = i1) → refl}) ]
  sigma-wcap = inc (λ l → ouc capA l , step1 l)
    where
    step0 step1 : ∀ l → B i (ouc capA l)

    step0 l = ouc
      (wfill (λ _ → B i (ouc capA l))
        (λ m → λ
          { (l = i0) → ouc capB m
          ; (l = i1) → ouc (uiBfill i1)
          ; (φ = i1) → uB i 1=1
          })
        i1
        (inc (ouc (uiBfill l)))
        i0)

    step1 l = ouc
      (wfill (λ _ → B i (ouc capA l))
        (λ m → λ
          { (l = i0) → ouc capB i0
          ; (l = i1) → ouc uiBcap m
          ; (φ = i1) → uB i 1=1
          })
        i0
        (inc (step0 l))
        i1)

module Pi {ℓ} (A : ∀ i → Set ℓ) (B : ∀ i → A i → Set ℓ)
  {φ : I}
  (u : ∀ i → Partial φ ((a : A i) → (B i a)))
  (i : I)
  (ui : ((a : A i) → B i a) [ φ ↦ u i ])
  where

  private
    module PiHelp (j : I) (aj : A j) where
      a : (i : I) → A i
      a i = ouc (wfill A {φ = i0} (λ _ ()) j (inc aj) i)

      acap : a j ≡ aj
      acap = ouc (wcap A {φ = i0} (λ _ ()) j (inc aj))

      fillB : B j (a j) [ φ ↦ (λ v → u j v (a j)) ]
      fillB = wfill (λ i → B i (a i)) (λ i v → u i v (a i)) i (inc (ouc ui (a i))) j

      fixfill : ∀ k → B j (acap k) [ φ ↦ (λ v → u j v (acap k)) ] → B j aj [ φ ↦ (λ v → u j v aj) ]
      fixfill k b = wfill (λ k → B j (acap k)) (λ k → λ {(φ = i1) → u j 1=1 (acap k)}) k b i1

      fix = fixfill i0

  pi-wfill : (j : I) → ((a : A j) → B j a) [ φ ↦ u j ]
  pi-wfill j = inc (λ aj → let open PiHelp j aj in ouc (fix fillB))

  private
    module _ (ai : A i) where
      open PiHelp i ai

      capB : (ouc fillB ≡ ouc ui (a i)) [ φ ↦ (λ {(φ = i1) → refl}) ]
      capB = wcap (λ i → B i (a i)) (λ i v → u i v (a i)) i (inc (ouc ui (a i)))

      fixcap : (b : B i ai [ φ ↦ (λ v → u i v ai) ])
        → (ouc (fixfill i1 b) ≡ ouc b) [ φ ↦ (λ {(φ = i1) → refl}) ]
      fixcap b = wcap (λ k → B i (acap k)) (λ k → λ {(φ = i1) → u i 1=1 (acap k)}) i1 b

      step0 : ouc (fix (inc (ouc ui (a i)))) ≡ ouc ui ai
      step0 k = ouc
        (wfill (λ _ → B i ai)
          (λ m → λ
            { (k = i0) → ouc (fix (inc (ouc ui (a i))))
            ; (k = i1) → ouc (fixcap (inc (ouc ui ai))) m
            ; (φ = i1) → u i 1=1 ai
            })
          i0
          (inc (ouc (fixfill k (inc (ouc ui (acap k))))))
          i1)

      step1 : ouc (fix fillB) ≡ ouc ui ai
      step1 k = ouc
        (wfill (λ _ → B i ai)
          (λ m → λ
            { (k = i0) → ouc (fix (inc (ouc capB m)))
            ; (k = i1) → ouc ui ai
            ; (φ = i1) → u i 1=1 ai
            })
          i1
          (inc (step0 k))
          i0)

  pi-wcap : (ouc (pi-wfill i) ≡ ouc ui) [ φ ↦ (λ {(φ = i1) → refl}) ]
  pi-wcap = inc (λ k ai → step1 ai k)

module Path {ℓ} (A : ∀ i → I → Set ℓ) (a0 : ∀ i → A i i0) (a1 : ∀ i → A i i1)
  {φ : I}
  (u : ∀ i → Partial φ (PathP (A i) (a0 i) (a1 i)))
  (i : I)
  (ui : (PathP (A i) (a0 i) (a1 i)) [ φ ↦ u i ])
  where

  path-wfill : (j : I) → (PathP (A j) (a0 j) (a1 j)) [ φ ↦ u j ]
  path-wfill j = inc (λ t → ouc
    (wfill (λ i → A i t)
      (λ k → λ {(φ = i1) → u k 1=1 t; (t = i0) → a0 k; (t = i1) → a1 k})
      i
      (inc (ouc ui t))
      j)
    )

  path-wcap : (ouc (path-wfill i) ≡ ouc ui) [ φ ↦ (λ {(φ = i1) → refl}) ]
  path-wcap = inc (λ k t → ouc
    (wcap (λ i → A i t)
      (λ k → λ {(φ = i1) → u k 1=1 t; (t = i0) → a0 k; (t = i1) → a1 k})
      i
      (inc (ouc ui t)))
    k)

{-# OPTIONS --cubical #-}
module Cubical.Experiments.BCHWeakCom where

open import Cubical.Core.Everything

module _ {ℓ} (A : I → Set ℓ) {φ : I} (u : ∀ i → Partial φ (A i)) where

  -- wcom

  wcom0 : (a : A i0 [ φ ↦ u i0 ]) (s : I) → A s [ φ ↦ u s ]
  wcom0 a s = inc (fill A u a s)

  wcom1 : (a : A i1 [ φ ↦ u i1 ]) (s : I) → A s [ φ ↦ u s ]
  wcom1 a s = inc (fill A u (inc (fill (λ i → A (~ i)) (λ i → u (~ i)) a i1)) s)

  wcomI : (a : (j : I) → A j [ φ ↦ u j ]) (j : I) (s : I) → A s [ φ ↦ u s ]
  wcomI a j s = inc (fill A u (inc squeeze) s)
    where
    a' : (i : I) → A i [ φ ↦ u i ]
    a' i = inc (fill (λ ~i → A (~ ~i)) (λ ~i → u (~ ~i)) (a i1) (~ i))

    squeeze : A i0
    squeeze =
      comp (λ ~i → A (~ ~i))
        (λ ~i → λ
          { (j = i0) → ouc (a (~ ~i))
          ; (j = i1) → ouc (a' (~ ~i))
          ; (φ = i1) → u (~ ~i) 1=1
          })
        (inc (ouc (a i1)))

  -- Check wcom coherence conditions. These must be reflexive.

  _ : (a : (j : I) → A j [ φ ↦ u j ]) (j : I) (s : I) → ouc (wcomI a i0 s) ≡ ouc (wcom0 (a i0) s)
  _ = λ a j s → refl

  _ : (a : (j : I) → A j [ φ ↦ u j ]) (j : I) (s : I) → ouc (wcomI a i1 s) ≡ ouc (wcom1 (a i1) s)
  _ = λ a j s → refl

  -- wcap

  wcap0 : (a : A i0 [ φ ↦ u i0 ]) → (ouc (wcom0 a i0) ≡ ouc a) [ φ ↦ (λ {(φ = i1) → refl}) ]
  wcap0 a = inc refl

  wcap1 : (a : A i1 [ φ ↦ u i1 ]) → (ouc (wcom1 a i1) ≡ ouc a) [ φ ↦ (λ {(φ = i1) → refl}) ]
  wcap1 a = inc (λ l →
    comp A
      (λ i → λ
        { (l = i0) → ouc (wcomI a' i i)
        ; (l = i1) → ouc (a' i)
        ; (φ = i1) → ouc (a' i)
        })
      (inc (ouc (a' i0)))
    )
   where
   a' : (i : I) → A i [ φ ↦ u i ]
   a' i = inc (fill (λ ~i → A (~ ~i)) (λ ~i → u (~ ~i)) a (~ i))

  -- Check wcap coherence conditions. These must be reflexive.

  wcapI : (a : (j : I) → A j [ φ ↦ u j ]) (j : I) → (ouc (wcomI a j j) ≡ ouc (a j)) [ φ ↦ (λ {(φ = i1) → refl}) ]
  wcapI a j = inc (λ l → c l j)
    where
    a' : (i : I) → A i [ φ ↦ u i ]
    a' i = inc (fill (λ ~i → A (~ ~i)) (λ ~i → u (~ ~i)) (a i1) (~ i))

    θ : (j k : I) → A j
    θ j k =
      fill (λ i → A (~ i))
        (λ ~j → λ
          { (k = i0) → ouc (a (~ ~j))
          ; (k = i1) → ouc (a' (~ ~j))
          ; (φ = i1) → u (~ ~j) 1=1
          })
        (inc (ouc (a i1)))
        (~ j)

    b : (l j : I) → A j
    b l j = fill A
      (λ j → λ
        { (l = i0) → ouc (wcomI (λ j → inc (θ j i1)) j j)
        ; (l = i1) → θ j i1
        ; (φ = i1) → u j 1=1
        })
      (inc (θ i0 i1))
      j

    test : (l : I) → b l i1 ≡ ouc (wcap1 (a i1)) l
    test l = refl

    c : (l j : I) → A j
    c l j = comp (λ _ → A j)
      (λ ~k → λ
        { (j = i0) → θ i0 (~ ~k)
        ; (j = i1) → ouc (wcap1 (a i1)) l
        ; (l = i0) → ouc (wcomI (λ j → inc (θ j (~ ~k))) j j)
        ; (l = i1) → θ j (~ ~k)
        ; (φ = i1) → u j 1=1
        })
      (inc (b l j))

  _ : (a : (j : I) → A j [ φ ↦ u j ]) (j : I) → ouc (wcapI a i0) ≡ ouc (wcap0 (a i0))
  _ = λ a j → refl

  _ : (a : (j : I) → A j [ φ ↦ u j ]) (j : I) → ouc (wcapI a i1) ≡ ouc (wcap1 (a i1))
  _ = λ a j → refl

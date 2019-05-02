{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Queue where

open import Agda.Builtin.List
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.List
open import Cubical.Data.Nat

-- move upstream

isOfHLevelPath : ∀ {ℓ} {A : Type ℓ} (n : ℕ)
  → isOfHLevel (suc n) A
  → {a₀ a₁ : A}
  → isOfHLevel n (a₀ ≡ a₁)
isOfHLevelPath zero levelA {a₀} {a₁} =
  (levelA a₀ a₁ , isProp→isSet levelA a₀ a₁ (levelA a₀ a₁))
isOfHLevelPath (suc n) levelA {a₀} {a₁} =
  levelA a₀ a₁
  
isOfHLevelPathP : ∀ {ℓ} (A : I → Type ℓ) (n : ℕ)
 → isOfHLevel (suc n) (A i0)
 → (a₀ : A i0) (a₁ : A i1)
 → isOfHLevel n (PathP A a₀ a₁)
isOfHLevelPathP A n levelA a₀ a₁ =
  subst
    (isOfHLevel n)
    (λ j → PathP (λ i → A (j ∧ i)) a₀ (transp (λ i → A (j ∨ ~ i)) j a₁))
    (isOfHLevelPath n levelA)

data 2ListQueue {ℓ} (A : Set ℓ) : Set ℓ where
  Q⟨_,_⟩ : (xs ys : List A) → 2ListQueue A
  tilt : ∀ xs ys z → Q⟨ xs ++ [ z ] , ys ⟩ ≡ Q⟨ xs , ys ++ [ z ] ⟩
  trunc : (q q' : 2ListQueue A) (α β : q ≡ q') → α ≡ β

module _ {ℓ} {A : Set ℓ} (sA : isSet A) where

  eval : 2ListQueue A → List A
  eval Q⟨ xs , ys ⟩ = xs ++ rev ys
  eval (tilt xs ys z i) = path i
    where
    path : (xs ++ [ z ]) ++ rev ys ≡ xs ++ rev (ys ++ [ z ])
    path =
      ++-assoc xs [ z ] (rev ys)
      ∙ cong (_++_ xs) (sym (rev-++ ys [ z ]))
  eval (trunc q q' α β i j) =
    isOfHLevelList 0 sA (eval q) (eval q') (cong eval α) (cong eval β) i j

  quot : List A → 2ListQueue A
  quot xs = Q⟨ xs , [] ⟩

  multitilt : (xs ys zs : List A) → Q⟨ xs ++ rev zs , ys ⟩ ≡ Q⟨ xs , ys ++ zs ⟩
  multitilt xs ys [] = cong₂ Q⟨_,_⟩ (++-unit-r xs) (sym (++-unit-r ys))
  multitilt xs ys (z ∷ zs) =
    cong (λ ws → Q⟨ ws , ys ⟩) (sym (++-assoc xs (rev zs) [ z ]))
    ∙ tilt (xs ++ rev zs) ys z
    ∙ multitilt xs (ys ++ [ z ]) zs
    ∙ cong (λ ws → Q⟨ xs , ws ⟩) (++-assoc ys [ z ] zs)

  quot∘eval : ∀ q → quot (eval q) ≡ q
  quot∘eval Q⟨ xs , ys ⟩ = multitilt xs [] ys
  quot∘eval (tilt xs ys z i) =
    isOfHLevelPathP
      (λ i → quot (eval (tilt xs ys z i)) ≡ tilt xs ys z i)
      0
      (trunc _ _ )
      (multitilt (xs ++ [ z ]) [] ys) (multitilt xs [] (ys ++ [ z ]))
      .fst i
  quot∘eval (trunc q q' α β i j) =
    isOfHLevelPathP
      (λ i →
        PathP (λ j → quot (eval (trunc q q' α β i j)) ≡ trunc q q' α β i j)
          (quot∘eval q) (quot∘eval q'))
      0
      (isOfHLevelPathP _ 1 (hLevelSuc 2 _ trunc _ _) _ _)
      (cong quot∘eval α) (cong quot∘eval β)
      .fst i j

  eval∘quot : ∀ xs → eval (quot xs) ≡ xs
  eval∘quot = ++-unit-r

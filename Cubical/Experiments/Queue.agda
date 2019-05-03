{-# OPTIONS --cubical --safe #-}
module Cubical.Experiments.Queue where

open import Agda.Builtin.List
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Prod
open import Cubical.Data.Sum
open import Cubical.Data.Unit

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

record QUEUE {ℓ} (A : Set ℓ) : Set (ℓ-suc ℓ) where
  field
    T : Set ℓ
    emp : T
    push : A → T → T
    pop : T → Unit ⊎ (T × A)

map-result : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''}
  → (B → C) → Unit ⊎ (B × A) → Unit ⊎ (C × A)
map-result f (inl tt) = inl tt
map-result f (inr (b , a)) = inr (f b , a)

map-result-∘ : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''} {D : Set ℓ'''}
  (g : C → D) (f : B → C)
  → ∀ r → map-result {A = A} g (map-result f r) ≡ map-result (λ b → g (f b)) r
map-result-∘ g f (inl tt) = refl
map-result-∘ g f (inr (b , a)) = refl

module 2List {ℓ} (A : Set ℓ) (sA : isSet A) where

  data Queue : Set ℓ where
    Q⟨_,_⟩ : (xs ys : List A) → Queue
    tilt : ∀ xs ys z → Q⟨ xs ++ [ z ] , ys ⟩ ≡ Q⟨ xs , ys ++ [ z ] ⟩
    trunc : (q q' : Queue) (α β : q ≡ q') → α ≡ β

  multitilt : (xs ys zs : List A) → Q⟨ xs ++ rev zs , ys ⟩ ≡ Q⟨ xs , ys ++ zs ⟩
  multitilt xs ys [] = cong₂ Q⟨_,_⟩ (++-unit-r xs) (sym (++-unit-r ys))
  multitilt xs ys (z ∷ zs) =
    cong (λ ws → Q⟨ ws , ys ⟩) (sym (++-assoc xs (rev zs) [ z ]))
    ∙ tilt (xs ++ rev zs) ys z
    ∙ multitilt xs (ys ++ [ z ]) zs
    ∙ cong (λ ws → Q⟨ xs , ws ⟩) (++-assoc ys [ z ] zs)

  -- push into the first list, pop from the second if possible

  emp : Queue
  emp = Q⟨ [] , [] ⟩

  push : A → Queue → Queue
  push a Q⟨ xs , ys ⟩ = Q⟨ a ∷ xs , ys ⟩
  push a (tilt xs ys z i) = tilt (a ∷ xs) ys z i
  push a (trunc q q' α β i j) =
    trunc _ _ (cong (push a) α) (cong (push a) β) i j

  popFlush : List A → Unit ⊎ (Queue × A)
  popFlush [] = inl tt
  popFlush (x ∷ xs) = inr (Q⟨ [] , xs ⟩ , x)

  pop : Queue → Unit ⊎ (Queue × A)
  pop Q⟨ xs , [] ⟩ = popFlush (rev xs)
  pop Q⟨ xs , y ∷ ys ⟩ = inr (Q⟨ xs , ys ⟩ , y)
  pop (tilt xs [] z i) = path i
    where
    path : popFlush (rev (xs ++ [ z ])) ≡ inr (Q⟨ xs , [] ⟩ , z)
    path =
      cong popFlush (rev-++ xs [ z ])
      ∙ cong (λ q → inr (q , z)) (sym (multitilt [] [] (rev xs)))
      ∙ cong (λ ys → inr (Q⟨ ys , [] ⟩ , z)) (rev-rev xs)
  pop (tilt xs (y ∷ ys) z i) = inr (tilt xs ys z i , y)
  pop (trunc q q' α β i j) =
    isOfHLevelSum 0
      (isProp→isSet isPropUnit)
      (hLevelProd 2 trunc sA)
      (pop q) (pop q') (cong pop α) (cong pop β)
      i j

  Q : QUEUE A
  Q = record { T = Queue ; emp = emp ; push = push ; pop = pop }

module 1List {ℓ} (A : Set ℓ) where

  Queue = List A

  emp : Queue
  emp = []

  push : A → Queue → Queue
  push = _∷_

  pop : Queue → Unit ⊎ (Queue × A)
  pop [] = inl tt
  pop (x ∷ []) = inr ([] , x)
  pop (x ∷ x' ∷ xs) = map-result (push x) (pop (x' ∷ xs))

  Q : QUEUE A
  Q = record { T = Queue ; emp = emp ; push = push ; pop = pop }

module Equivalence {ℓ} (A : Set ℓ) (sA : isSet A) where

  module Two = 2List A sA
  module One = 1List A

  open Two using (Q⟨_,_⟩ ; tilt ; trunc ; multitilt)

  eval : Two.Queue → One.Queue
  eval Q⟨ xs , ys ⟩ = xs ++ rev ys
  eval (tilt xs ys z i) = path i
    where
    path : (xs ++ [ z ]) ++ rev ys ≡ xs ++ rev (ys ++ [ z ])
    path =
      ++-assoc xs [ z ] (rev ys)
      ∙ cong (_++_ xs) (sym (rev-++ ys [ z ]))
  eval (trunc q q' α β i j) =
    isOfHLevelList 0 sA (eval q) (eval q') (cong eval α) (cong eval β) i j

  quot : One.Queue → Two.Queue
  quot xs = Q⟨ xs , [] ⟩

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

  quot∘emp : quot One.emp ≡ Two.emp
  quot∘emp = refl

  quot∘push : ∀ a q → quot (One.push a q) ≡ Two.push a (quot q)
  quot∘push a q = refl

  equiv : One.Queue ≃ Two.Queue
  equiv =
    isoToEquiv
      (iso quot eval quot∘eval eval∘quot)

  same : One.Q ≡ Two.Q
  same i = record
    { T = ua equiv i
    ; emp =
      glue (λ {(i = i0) → One.emp; (i = i1) → Two.emp}) Two.emp
    ; push = λ a g →
      glue (λ {(i = i0) → One.push a g; (i = i1) → Two.push a g}) (Two.push a (unglue (i ∨ ~ i) g))
    ; pop =
      {!!}
    }

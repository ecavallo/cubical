{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Data.Queue.Base where

open import Cubical.Foundations.Everything

open import Cubical.Foundations.SIP
open import Cubical.Structures.Queue

open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.List
open import Cubical.Data.Sigma

module _ (A : Type ℓ) (Aset : isSet A) where
 open Queues-on A Aset

 -- lemma
 -- following Cavallo we can now define 1Lists and 2Lists as Queues on A
 -- and prove that there is a queue-iso between them, this then gives us a path
 1List : Queue
 1List = (Q , emp , enq , deq)
  where
   Q = List A
   emp = []
   enq = _∷_
   deq : Q → Unit ⊎ (Q × A)
   deq [] = inl tt
   deq (x ∷ []) = inr ([] , x)
   deq (x ∷ x' ∷ xs) = deq-map-forward (enq x) (deq (x' ∷ xs))

 -- for later convenience
 Q₁ = typ 1List
 emp₁ = str 1List .fst
 enq₁ = str 1List .snd .fst
 deq₁ = str 1List .snd .snd


 -- Now for 2Lists
 data Q₂ : Set ℓ where
   Q₂⟨_,_⟩ : (xs ys : List A) → Q₂
   tilt : ∀ xs ys z → Q₂⟨ xs ++ [ z ] , ys ⟩ ≡ Q₂⟨ xs , ys ++ [ z ] ⟩

  -- enq into the first list, deq from the second if possible

 flushEq' : (xs ys : List A) → Q₂⟨ xs ++ ys , [] ⟩ ≡ Q₂⟨ xs , rev ys ⟩
 flushEq' xs [] = cong Q₂⟨_, [] ⟩ (++-unit-r xs)
 flushEq' xs (z ∷ ys) j =
   hcomp
     (λ i → λ
       { (j = i0) → Q₂⟨ ++-assoc xs [ z ] ys i , [] ⟩
       ; (j = i1) → tilt xs (rev ys) z i
       })
     (flushEq' (xs ++ [ z ]) ys j)

 flushEq : (xs ys : List A) → Q₂⟨ xs ++ rev ys , [] ⟩ ≡ Q₂⟨ xs , ys ⟩
 flushEq xs ys = flushEq' xs (rev ys) ∙ cong Q₂⟨ xs ,_⟩ (rev-rev ys)

 emp₂ : Q₂
 emp₂ = Q₂⟨ [] , [] ⟩

 enq₂ : A → Q₂ → Q₂
 enq₂ a Q₂⟨ xs , ys ⟩ = Q₂⟨ a ∷ xs , ys ⟩
 enq₂ a (tilt xs ys z i) = tilt (a ∷ xs) ys z i

 deq₂Flush : List A → Unit ⊎ (Q₂ × A)
 deq₂Flush [] = inl tt
 deq₂Flush (x ∷ xs) = inr (Q₂⟨ [] , xs ⟩ , x)

 deq₂ : Q₂ → Unit ⊎ (Q₂ × A)
 deq₂ Q₂⟨ xs , [] ⟩ = deq₂Flush (rev xs)
 deq₂ Q₂⟨ xs , y ∷ ys ⟩ = inr (Q₂⟨ xs , ys ⟩ , y)
 deq₂ (tilt xs [] z i) = path i
   where
   path : deq₂Flush (rev (xs ++ [ z ])) ≡ inr (Q₂⟨ xs , [] ⟩ , z)
   path =
     cong deq₂Flush (rev-snoc xs z)
     ∙ cong (λ q → inr (q , z)) (sym (flushEq' [] xs))
 deq₂ (tilt xs (y ∷ ys) z i) = inr (tilt xs ys z i , y)

 2List : Queue
 2List = (Q₂ , emp₂ , enq₂ , deq₂)

 -- We construct an equivalence Q₁≃Q₂ and prove that this is a queue-iso
 quot : Q₁ → Q₂
 quot xs = Q₂⟨ xs , [] ⟩

 eval : Q₂ → Q₁
 eval Q₂⟨ xs , ys ⟩ = xs ++ rev ys
 eval (tilt xs ys z i) =
   hcomp
     (λ j → λ
       { (i = i0) → (xs ++ [ z ]) ++ rev ys
       ; (i = i1) → xs ++ rev-snoc ys z (~ j)
       })
     (++-assoc xs [ z ] (rev ys) i)
 
 quot∘eval : ∀ q → quot (eval q) ≡ q
 quot∘eval Q₂⟨ xs , ys ⟩ = flushEq xs ys
 quot∘eval (tilt xs ys z i) j =
   hcomp
     (λ k → λ
       { (i = i0) →
         compPath-filler (flushEq' (xs ++ [ z ]) (rev ys)) (cong Q₂⟨ xs ++ [ z ] ,_⟩ (rev-rev ys)) k j
       ; (i = i1) → helper k
       ; (j = i0) →
         Q₂⟨ compPath-filler (++-assoc xs [ z ] (rev ys)) (cong (xs ++_) (sym (rev-snoc ys z))) k i , [] ⟩
       ; (j = i1) → tilt xs (rev-rev ys k) z i
       })
     flushEq'-filler
   where
   flushEq'-filler : Q₂
   flushEq'-filler =
     hfill
       (λ i → λ
         { (j = i0) → Q₂⟨ ++-assoc xs [ z ] (rev ys) i , [] ⟩
         ; (j = i1) → tilt xs (rev (rev ys)) z i
         })
       (inS (flushEq' (xs ++ [ z ]) (rev ys) j))
       i

   helper : I → Q₂
   helper k =
     hcomp
       (λ l → λ
         { (j = i0) → Q₂⟨ xs ++ rev-snoc ys z (l ∧ ~ k) , [] ⟩
         ; (j = i1) → Q₂⟨ xs , rev-rev-snoc ys z l k ⟩
         ; (k = i0) → flushEq' xs (rev-snoc ys z l) j
         ; (k = i1) → flushEq xs (ys ++ [ z ]) j
         })
       (compPath-filler (flushEq' xs (rev (ys ++ [ z ]))) (cong Q₂⟨ xs ,_⟩ (rev-rev (ys ++ [ z ]))) k j)

 eval∘quot : ∀ xs → eval (quot xs) ≡ xs
 eval∘quot = ++-unit-r


 -- We get our desired equivalence
 quotEquiv : Q₁ ≃ Q₂
 quotEquiv = isoToEquiv (iso quot eval quot∘eval eval∘quot)

 -- Now it only remains to prove that this is a queue-iso
 quot∘emp : quot emp₁ ≡ emp₂
 quot∘emp = refl

 quot∘enq : ∀ x xs → quot (enq₁ x xs) ≡ enq₂ x (quot xs)
 quot∘enq x xs = refl


 quot∘deq : ∀ xs → deq-map-forward quot (deq₁ xs) ≡ deq₂ (quot xs)
 quot∘deq [] = refl
 quot∘deq (x ∷ []) = refl
 quot∘deq (x ∷ x' ∷ xs) =
   deq-map-forward-∘ quot (enq₁ x) (deq₁ (x' ∷ xs))
   ∙ sym (deq-map-forward-∘ (enq₂ x) quot (deq₁ (x' ∷ xs)))
   ∙ cong (deq-map-forward (enq₂ x)) (quot∘deq (x' ∷ xs))
   ∙ lemma x x' (rev xs)
   where
   lemma : ∀ x x' ys
     → deq-map-forward (enq₂ x) (deq₂Flush (ys ++ [ x' ]))
       ≡ deq₂Flush ((ys ++ [ x' ]) ++ [ x ])
   lemma x x' [] i = inr (tilt [] [] x i , x')
   lemma x x' (y ∷ ys) i = inr (tilt [] (ys ++ [ x' ]) x i , y)


 quotEquiv-is-queue-iso : queue-iso 1List 2List quotEquiv
 quotEquiv-is-queue-iso = quot∘emp , quot∘enq , quot∘deq


 -- And we get the desired Path
 Path-1List-2List : 1List ≡ 2List
 Path-1List-2List = sip Queue-is-SNS 1List 2List (quotEquiv , quotEquiv-is-queue-iso)

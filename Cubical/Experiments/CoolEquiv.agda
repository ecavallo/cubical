{-# OPTIONS --cubical --safe #-}
module Cubical.Experiments.CoolEquiv where

open import Cubical.Core.Everything
open import Cubical.Foundations.Isomorphism

record isCoolEquiv {A B : Set} (f : A → B) : Set where
  constructor cool-equiv
  field
    inv : B → A
    rightInv : ∀ b → f (inv b) ≡ b
    leftInv : ∀ a → inv (f a) ≡ a
    adj : ∀ a → PathP (λ i → f (leftInv a i) ≡ f a) (rightInv (f a)) refl

open isCoolEquiv public

CoolEquiv : Set → Set → Set
CoolEquiv A B = Σ[ f ∈ (A → B) ] (isCoolEquiv f)

contractFiber : {A B : Set} (f : A → B) (ise : isCoolEquiv f) (a : A)
  → Path (fiber f (f a)) (ise .inv (f a) , ise .rightInv (f a)) (a , refl)
contractFiber f ise a = λ i → (ise .leftInv a i , ise .adj a i)

idCoolEquiv : (A : Set) → CoolEquiv A A
idCoolEquiv A =
  (idfun A , cool-equiv (idfun A) (λ _ → refl) (λ _ → refl) (λ _ → refl))

IsoToCoolEquiv : {A B : Set} → Iso A B → CoolEquiv A B
IsoToCoolEquiv {A} {B} (iso f g α β) =
  ( f
  , record
    { inv = g
    ; rightInv = α
    ; leftInv = λ a i → aux a i i1
    ; adj = λ a i j →
      hcomp
        (λ k → λ
          { (i = i0) → α (f (β a k)) j
          ; (i = i1) → filler a k j
          ; (j = i0) → f (aux a i k)
          ; (j = i1) → filler a k i
          })
        (α (α (f a) i) j)
    }
  )
  where
  aux : A → I → I → A
  aux a i =
    hfill
      (λ k → λ
        { (i = i0) → g (f (β a k))
        ; (i = i1) → β a k
        })
      (inS (g (α (f a) i)))

  filler : A → I → I → B
  filler a k =
    hfill
      (λ m → λ
        { (k = i0) → α (f a) m
        ; (k = i1) → f a
        })
      (inS (f (β a k)))

isPropIsCoolEquiv : {A : Set} {B : Set} (f : A → B) → isProp (isCoolEquiv f)
isPropIsCoolEquiv {A} {B} f (cool-equiv g α β adj) (cool-equiv g' α' β' adj') i =
  record
  { inv = λ b → invFiller b i1
  ; rightInv = λ b j → rightInvFiller b j i1
  ; leftInv = λ a j → leftInvFiller a j i1
  ; adj = λ a l j →
    hcomp
    (λ k → λ
      { (i = i0) → rightAuxAdj a j k l
      ; (i = i1) → leftAuxAdj a j k l
      ; (j = i0) → f (leftInvFiller a l k)
      ; (j = i1) → adj a l k
    --; (l = i0) → rightInvFiller (f a) j k  -- redundant
      ; (l = i1) → adj' a k j
      })
    (α' (f (β a l)) j)
  }
  where
  invFiller : (b : B) → (I → A)
  invFiller b =
    hfill
      (λ k → λ
        { (i = i0) → β' (g b) k
        ; (i = i1) → g' (α b k)
        })
      (inS (g' (f (g b))))

  rightAux : (b : B) → I → I → (I → B)
  rightAux b j k =
    hfill
      (λ m → λ
        { (j = i0) → f (β' (g b) k)
        ; (j = i1) → α b (k ∧ m)
        ; (k = i0) → α' (f (g b)) j
        ; (k = i1) → α b (j ∧ m)
        })
      (inS (adj' (g b) k j))

  rightInvFiller : (b : B) → I → (I → B)
  rightInvFiller b j =
    hfill
      (λ k → λ
        { (i = i0) → rightAux b j k i1
        ; (i = i1) → α' (α b k) j
        ; (j = i0) → f (invFiller b k)
        ; (j = i1) → α b k
        })
      (inS (α' (f (g b)) j))

  rightAuxAdj : (a : A) → I → I → I → B
  rightAuxAdj a j k l =
    hcomp
      (λ m → λ
        { (j = i0) → f (β' (β a l) k)
        ; (j = i1) → adj a l (k ∧ m)
        ; (k = i0) → α' (f (β a l)) j
        ; (k = i1) → adj a l (j ∧ m)
      --; (l = i0) → rightAux (f a) j k m  -- redundant
        ; (l = i1) → adj' a k j
        })
      (adj' (β a l) k j)

  leftAux : (a : A) → I → I → (I → A)
  leftAux a j k =
    hfill
      (λ m → λ
        { (j = i0) → g' (α (f a) k)
        ; (j = i1) → β' a (k ∧ m)
        ; (k = i0) → g' (f (β a j))
        ; (k = i1) → β' a (j ∧ m)
        })
      (inS (g' (adj a j k)))

  leftInvFiller : (a : A) → I → (I → A)
  leftInvFiller a j =
    hfill
      (λ k → λ
        { (i = i0) → β' (β a j) k
        ; (i = i1) → leftAux a j k i1
      --; (j = i0) → invFiller (f a) k  -- redundant
        ; (j = i1) → β' a k
        })
      (inS (g' (f (β a j))))

  leftAuxAdj : (a : A) → I → I → I → B
  leftAuxAdj a j k l =
    hcomp
      (λ m → λ
        { (l = i0) → α' (α (f a) k) j
        ; (l = i1) → adj' a (k ∧ m) j
        ; (k = i0) → α' (f (β a l)) j
        ; (k = i1) → adj' a (l ∧ m) j
        ; (j = i0) → f (leftAux a l k m)
        ; (j = i1) → adj a l k
        })
      (α' (adj a l k) j)

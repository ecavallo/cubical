{-# OPTIONS --cubical #-}
module Cubical.Test where

open import Cubical.Foundations.Everything
open import Cubical.HITs.S1
open import Cubical.HITs.Susp

Code : Susp S¹ → Type
Code north = S¹
Code south = S¹
Code (merid a i) = ua (rot a , rotIsEquiv a) i

encodo : north ≡ south → S¹
encodo p = subst Code p base

whoa : (a : S¹) → encodo (merid a) ≡ a
whoa base = refl
whoa (loop _) = refl

incredible : (a b : S¹) → Path (Path (Susp S¹) north south) (merid a) (merid b) → a ≡ b
incredible a b p = sym (whoa a) ∙ cong encodo p ∙ whoa b

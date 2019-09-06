{-# OPTIONS --cubical --safe #-}

module Cubical.Experiments.IntTrouble where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Int

infixl 5 _⊖_
data DeltaInt : Type₀ where
  _⊖_    : ℕ → ℕ → DeltaInt
  cancel : ∀ a b → a ⊖ b ≡ suc a ⊖ suc b

fromℕ : ℕ → DeltaInt
fromℕ n = n ⊖ 0

fromInt : Int → DeltaInt
fromInt (pos n) = fromℕ n
fromInt (negsuc n) = 0 ⊖ suc n

toInt : DeltaInt → Int
toInt (x ⊖ y) = x ℕ- y
toInt (cancel a b i) = a ℕ- b

deltaIntRet : ∀ a → fromInt (toInt a) ≡ a
deltaIntRet (x ⊖ 0) = refl
deltaIntRet (0 ⊖ suc y) = refl
deltaIntRet (suc a ⊖ suc b) = deltaIntRet (a ⊖ b) ∙ cancel a b
deltaIntRet (cancel a b i) j = compPath-filler (deltaIntRet (a ⊖ b)) (cancel a b) i j

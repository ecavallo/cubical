{-# OPTIONS --cubical --safe --no-import-sorts #-}
module Cubical.Categories.Cube where

{- Definitions of the cartesian, Dedekind, and De Morgan cube categories -}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Vec as V

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base

open Precategory
open Functor
open NatTrans

{- Cartesian -}

module Cartesian where
  𝕀 : ℕ → Type
  𝕀 m = Fin m ⊎ Bool

  end : ∀ {m} → Bool → 𝕀 m
  end = inr

  var : ∀ {m} → 𝕀 (suc m)
  var = inl zero

  weak𝕀 : ∀ {m} → 𝕀 m → 𝕀 (suc m)
  weak𝕀 = ⊎.map suc (idfun _)

  [_,_] : ℕ → ℕ → Type
  [ m , n ] = Vec (𝕀 m) n

  weak : ∀ {m n} → [ m , n ] → [ suc m , n ]
  weak [] = []
  weak (r ∷ f) = weak𝕀 r ∷ weak f

  idC : ∀ n → [ n , n ]
  idC zero = []
  idC (suc n) = var ∷ weak (idC n)

  _[_] : ∀ {m n} → 𝕀 n → [ m , n ] → 𝕀 m
  inl zero [ s ∷ f ] = s
  inl (suc x) [ s ∷ f ] = inl x [ f ]
  inr b [ f ] = inr b

  [weak] : ∀ {m n} (r : 𝕀 n) (f : [ m , n ]) → r [ weak f ] ≡ weak𝕀 (r [ f ])
  [weak] (inl zero) (s ∷ f) = refl
  [weak] (inl (suc x)) (s ∷ f) = [weak] (inl x) f
  [weak] (inr _) f = refl

  [id] : ∀ {n} (r : 𝕀 n) → r [ idC n ] ≡ r
  [id] (inl zero) = refl
  [id] (inl (suc x)) = ([weak] (inl x) (idC _)) ∙ cong weak𝕀 ([id] (inl x))
  [id] (inr b) = refl

  beta𝕀 : ∀ {m n} (r : 𝕀 n) (s : 𝕀 m) (f : [ m , n ])
    → weak𝕀 r [ s ∷ f ] ≡ r [ f ]
  beta𝕀 (inl _) _ _ = refl
  beta𝕀 (inr _) _ _ = refl

  _∘C_ : ∀ {m n p} → [ n , p ] → [ m , n ] → [ m , p ]
  [] ∘C f = []
  (r ∷ g) ∘C f = r [ f ] ∷ g ∘C f

  beta : ∀ {m n p} (g : [ n , p ]) (r : 𝕀 m) (f : [ m , n ])
    → (weak g ∘C (r ∷ f)) ≡ g ∘C f
  beta [] r f = refl
  beta (s ∷ g) r f = cong₂ _∷_ (beta𝕀 s r f) (beta g r f)

  [∘] : ∀ {m n p} (r : 𝕀 p) (g : [ n , p ]) (f : [ m , n ])
    → r [ g ∘C f ] ≡ (r [ g ]) [ f ]
  [∘] (inl zero) (s ∷ g) f = refl
  [∘] (inl (suc x)) (s ∷ g) f = [∘] (inl x) g f
  [∘] (inr _) g f = refl

  idL : ∀ {m n} (f : [ m , n ]) → (idC n) ∘C f ≡ f
  idL [] = refl
  idL (r ∷ f) = cong (r ∷_) (beta (idC _) r f ∙ idL f)

  idR : ∀ {m n} (f : [ m , n ]) → f ∘C (idC m) ≡ f
  idR [] = refl
  idR (r ∷ f) = cong₂ _∷_ ([id] r) (idR f)

  assocC : ∀ {m n p q} (h : [ p , q ]) (g : [ n , p ]) (f : [ m , n ])
    → h ∘C (g ∘C f) ≡ (h ∘C g) ∘C f
  assocC [] g f = refl
  assocC (r ∷ h) g f = cong₂ _∷_ ([∘] r g f) (assocC h g f)

  Cat : Precategory ℓ-zero ℓ-zero
  Cat .ob = ℕ
  Cat .Hom[_,_] = [_,_]
  Cat .id = idC
  Cat ._⋆_ f g = g ∘C f
  Cat .⋆IdL = idR
  Cat .⋆IdR = idL
  Cat .⋆Assoc f g h = assocC h g f

  instance
    isCat : isCategory Cat
    isCat .isSetHom =
      isOfHLevelRespectEquiv 2
        (FinVec≃Vec _)
        (isSetΠ λ _ → isOfHLevelSum 0 isSetFin isSetBool)

{- De Morgan -}

module DeMorgan where

  𝔹 : ℕ → Type
  𝔹 n = Vec Bool n

  𝕀 : ℕ → Type
  𝕀 n = 𝔹 n → Bool

  end : ∀ {m} → Bool → 𝕀 m
  end b _ = b

  var : ∀ {m} → 𝕀 (suc m)
  var (b ∷ v) = b

  weak𝕀 : ∀ {m} → 𝕀 m → 𝕀 (suc m)
  weak𝕀 f (b ∷ v) = f v

  weakEnd : ∀ {m} (b : Bool) → weak𝕀 (end {m} b) ≡ end b
  weakEnd b = funExt λ {(_ ∷ v) → refl}

  [_,_] : ℕ → ℕ → Type
  [ m , n ] = Vec (𝕀 m) n

  weak : ∀ {m n} → [ m , n ] → [ suc m , n ]
  weak [] = []
  weak (r ∷ f) = weak𝕀 r ∷ weak f

  idM : ∀ n → [ n , n ]
  idM zero = []
  idM (suc n) = var ∷ weak (idM n)

  ⟦_⟧ : ∀ {m n} → [ m , n ] → 𝔹 m → 𝔹 n
  ⟦ [] ⟧ v = []
  ⟦ r ∷ f ⟧ v = (r v) ∷ ⟦ f ⟧ v

  beta𝔹 : ∀ {m n} (f : [ m , n ]) (b : Bool) (v : 𝔹 m)
    → ⟦ weak f ⟧ (b ∷ v) ≡ ⟦ f ⟧ v
  beta𝔹 [] b v = refl
  beta𝔹 (r ∷ f) b v = cong (r v ∷_) (beta𝔹 f b v)

  ⟦id⟧ : ∀ {n} (v : 𝔹 n) → ⟦ idM n ⟧ v ≡ v
  ⟦id⟧ [] = refl
  ⟦id⟧ (b ∷ v) = cong (b ∷_) (beta𝔹 (idM _) b v ∙ ⟦id⟧ v)

  _[_] : ∀ {m n} → 𝕀 n → [ m , n ] → 𝕀 m
  (r [ f ]) v = r (⟦ f ⟧ v)

  [id] : ∀ {n} (r : 𝕀 n) → r [ idM n ] ≡ r
  [id] r = funExt λ v → cong r (⟦id⟧ v)

  _∘M_ : ∀ {m n p} → [ n , p ] → [ m , n ] → [ m , p ]
  [] ∘M f = []
  (r ∷ g) ∘M f = r [ f ] ∷ g ∘M f

  ⟦∘⟧ : ∀ {m n p} (v : 𝔹 m) (g : [ n , p ]) (f : [ m , n ])
    → ⟦ g ∘M f ⟧ v ≡ ⟦ g ⟧ (⟦ f ⟧ v)
  ⟦∘⟧ v [] f = refl
  ⟦∘⟧ v (r ∷ g) f = cong (r (⟦ f ⟧ v) ∷_) (⟦∘⟧ v g f)

  beta : ∀ {m n p} (g : [ n , p ]) (r : 𝕀 m) (f : [ m , n ])
    → (weak g ∘M (r ∷ f)) ≡ g ∘M f
  beta [] r f = refl
  beta (s ∷ g) r f = cong (s [ f ] ∷_) (beta g r f)

  [∘] : ∀ {m n p} (r : 𝕀 p) (g : [ n , p ]) (f : [ m , n ])
    → r [ g ∘M f ] ≡ (r [ g ]) [ f ]
  [∘] r g f = funExt λ v → cong r (⟦∘⟧ v g f)

  idL : ∀ {m n} (f : [ m , n ]) → (idM n) ∘M f ≡ f
  idL [] = refl
  idL (r ∷ f) = cong (r ∷_) (beta (idM _) r f ∙ idL f)

  idR : ∀ {m n} (f : [ m , n ]) → f ∘M (idM m) ≡ f
  idR [] = refl
  idR (r ∷ f) = cong₂ _∷_ ([id] r) (idR f)

  assocM : ∀ {m n p q} (h : [ p , q ]) (g : [ n , p ]) (f : [ m , n ])
    → h ∘M (g ∘M f) ≡ (h ∘M g) ∘M f
  assocM [] g f = refl
  assocM (r ∷ h) g f = cong₂ _∷_ ([∘] r g f) (assocM h g f)

  Cat : Precategory ℓ-zero ℓ-zero
  Cat .ob = ℕ
  Cat .Hom[_,_] = [_,_]
  Cat .id = idM
  Cat ._⋆_ f g = g ∘M f
  Cat .⋆IdL = idR
  Cat .⋆IdR = idL
  Cat .⋆Assoc f g h = assocM h g f

  instance
    isCat : isCategory Cat
    isCat .isSetHom =
      isOfHLevelRespectEquiv 2
        (FinVec≃Vec _)
        (isSetΠ λ _ →
          (isSetΠ λ _ → isSetBool))

{- Dedekind -}

module Dedekind where

  private
    module M = DeMorgan

  open DeMorgan public using (𝔹)

  data _⊑_ : Bool → Bool → Type where
    false⊑ : (b : Bool) → false ⊑ b
    true⊑ : true ⊑ true

  id⊑ : ∀ b → b ⊑ b
  id⊑ false = false⊑ false
  id⊑ true = true⊑

  data _⊑V_ : ∀ {n} → Vec Bool n → Vec Bool n → Type where
    []⊑ : [] ⊑V []
    _∷⊑_ : ∀ {n b b'} {v v' : Vec Bool n} → b ⊑ b' → v ⊑V v' → (b ∷ v) ⊑V (b' ∷ v')

  id⊑V : ∀ {n : ℕ} → (v : Vec Bool n) → v ⊑V v
  id⊑V [] = []⊑
  id⊑V (b ∷ v) = id⊑ b ∷⊑ id⊑V v

  isProp⊑ : ∀ {b b'} → isProp (b ⊑ b')
  isProp⊑ (false⊑ _) (false⊑ _) = refl
  isProp⊑ true⊑ true⊑ = refl

  isMonotone : ∀ {n} (f : 𝔹 n → Bool) → Type
  isMonotone f = ∀ {v v'} → v ⊑V v' → f v ⊑ f v'

  𝕀 : ℕ → Type
  𝕀 n = Σ[ f ∈ M.𝕀 n ] (isMonotone f)

  isPropIsMonotone : ∀ {n} (f : 𝔹 n → Bool) → isProp (isMonotone f)
  isPropIsMonotone f =
    isPropImplicitΠ λ _ →
    isPropImplicitΠ λ _ →
    isPropΠ λ _ →
    isProp⊑

  𝕀≡ : {n : ℕ} {f g : 𝕀 n} → f .fst ≡ g .fst → f ≡ g
  𝕀≡ = Σ≡Prop λ _ → isPropIsMonotone _

  end : ∀ {m} → Bool → 𝕀 m
  end b .fst = M.end b
  end b .snd _ = id⊑ b

  var : ∀ {m} → 𝕀 (suc m)
  var .fst = M.var
  var .snd (leq ∷⊑ _) = leq

  weak𝕀 : ∀ {m} → 𝕀 m → 𝕀 (suc m)
  weak𝕀 f .fst = M.weak𝕀 (f .fst)
  weak𝕀 f .snd (_ ∷⊑ leq) = f .snd leq

  weakEnd : ∀ {m} (b : Bool) → weak𝕀 (end {m} b) ≡ end b
  weakEnd b = 𝕀≡ (M.weakEnd b)

  [_,_] : ℕ → ℕ → Type
  [ m , n ] = Vec (𝕀 m) n

  weak : ∀ {m n} → [ m , n ] → [ suc m , n ]
  weak [] = []
  weak (r ∷ f) = weak𝕀 r ∷ weak f

  idD : ∀ n → [ n , n ]
  idD zero = []
  idD (suc n) = var ∷ weak (idD n)

  ⟦_⟧ : ∀ {m n} → [ m , n ] → 𝔹 m → 𝔹 n
  ⟦ f ⟧ = M.⟦ V.map fst f ⟧

  ⟦_⟧⊑ : ∀ {m n} {v v' : 𝔹 m}
    → (f : [ m , n ]) → v ⊑V v' → ⟦ f ⟧ v ⊑V ⟦ f ⟧ v'
  ⟦ [] ⟧⊑ leq = []⊑
  ⟦ r ∷ f ⟧⊑ leq = r .snd leq ∷⊑ ⟦ f ⟧⊑ leq

  beta𝔹 : ∀ {m n} (f : [ m , n ]) (b : Bool) (v : 𝔹 m)
    → ⟦ weak f ⟧ (b ∷ v) ≡ ⟦ f ⟧ v
  beta𝔹 [] b v = refl
  beta𝔹 (r ∷ f) b v = cong (r .fst v ∷_) (beta𝔹 f b v)

  ⟦id⟧ : ∀ {n} (v : 𝔹 n) → ⟦ idD n ⟧ v ≡ v
  ⟦id⟧ [] = refl
  ⟦id⟧ (b ∷ v) = cong (b ∷_) (beta𝔹 (idD _) b v ∙ ⟦id⟧ v)

  _[_] : ∀ {m n} → 𝕀 n → [ m , n ] → 𝕀 m
  (r [ f ]) .fst v = r .fst (⟦ f ⟧ v)
  (r [ f ]) .snd leq = r .snd (⟦ f ⟧⊑ leq)

  [id] : ∀ {n} (r : 𝕀 n) → r [ idD n ] ≡ r
  [id] r = 𝕀≡ (funExt λ v → cong (r .fst) (⟦id⟧ v))

  _∘D_ : ∀ {m n p} → [ n , p ] → [ m , n ] → [ m , p ]
  [] ∘D f = []
  (r ∷ g) ∘D f = r [ f ] ∷ g ∘D f

  ⟦∘⟧ : ∀ {m n p} (v : 𝔹 m) (g : [ n , p ]) (f : [ m , n ])
    → ⟦ g ∘D f ⟧ v ≡ ⟦ g ⟧ (⟦ f ⟧ v)
  ⟦∘⟧ v [] f = refl
  ⟦∘⟧ v (r ∷ g) f = cong (r .fst (⟦ f ⟧ v) ∷_) (⟦∘⟧ v g f)

  beta : ∀ {m n p} (g : [ n , p ]) (r : 𝕀 m) (f : [ m , n ])
    → (weak g ∘D (r ∷ f)) ≡ g ∘D f
  beta [] r f = refl
  beta (s ∷ g) r f = cong (s [ f ] ∷_) (beta g r f)

  [∘] : ∀ {m n p} (r : 𝕀 p) (g : [ n , p ]) (f : [ m , n ])
    → r [ g ∘D f ] ≡ (r [ g ]) [ f ]
  [∘] r g f = 𝕀≡ (funExt λ v → cong (r .fst) (⟦∘⟧ v g f))

  idL : ∀ {m n} (f : [ m , n ]) → (idD n) ∘D f ≡ f
  idL [] = refl
  idL (r ∷ f) = cong (r ∷_) (beta (idD _) r f ∙ idL f)

  idR : ∀ {m n} (f : [ m , n ]) → f ∘D (idD m) ≡ f
  idR [] = refl
  idR (r ∷ f) = cong₂ _∷_ ([id] r) (idR f)

  assocD : ∀ {m n p q} (h : [ p , q ]) (g : [ n , p ]) (f : [ m , n ])
    → h ∘D (g ∘D f) ≡ (h ∘D g) ∘D f
  assocD [] g f = refl
  assocD (r ∷ h) g f = cong₂ _∷_ ([∘] r g f) (assocD h g f)

  Cat : Precategory ℓ-zero ℓ-zero
  Cat .ob = ℕ
  Cat .Hom[_,_] = [_,_]
  Cat .id = idD
  Cat ._⋆_ f g = g ∘D f
  Cat .⋆IdL = idR
  Cat .⋆IdR = idL
  Cat .⋆Assoc f g h = assocD h g f

  instance
    isCat : isCategory Cat
    isCat .isSetHom =
      isOfHLevelRespectEquiv 2
        (FinVec≃Vec _)
        (isSetΠ λ _ →
          isSetΣ
            (isSetΠ λ _ → isSetBool)
            (λ _ → isProp→isSet (isPropIsMonotone _)))

{- Cartesian → Dedekind inclusion -}

module Cartesian→Dedekind where

  private
    module C = Cartesian
    module D = Dedekind

  𝕀 : ∀ {n} → C.𝕀 n → D.𝕀 n
  𝕀 (inl zero) = D.var
  𝕀 (inl (suc x)) = D.weak𝕀 (𝕀 (inl x))
  𝕀 (inr b) = D.end b

  ι : ∀ {m n} → C.[ m , n ] → D.[ m , n ]
  ι [] = []
  ι (r ∷ f) = 𝕀 r ∷ ι f

  weak : ∀ {m n} (f : C.[ m , n ])
    → ι (C.weak f) ≡ D.weak (ι f)
  weak [] = refl
  weak (inl x ∷ f) = cong (D.weak𝕀 (𝕀 (inl x)) ∷_) (weak f)
  weak (inr b ∷ f) = cong₂ _∷_ (sym (D.weakEnd b)) (weak f)

  idι : ∀ n → ι (C.idC n) ≡ D.idD n
  idι zero = refl
  idι (suc n) = cong (D.var ∷_) (weak (C.idC n) ∙ cong D.weak (idι n))

  𝕀[] : ∀ {m n} (r : C.𝕀 n) (f : C.[ m , n ])
    → 𝕀 (r C.[ f ]) ≡ (𝕀 r) D.[ ι f ]
  𝕀[] (inl zero) (s ∷ f) = refl
  𝕀[] (inl (suc x)) (s ∷ f) = 𝕀[] (inl x) f
  𝕀[] (inr b) f = refl

  ι∘ : ∀ {m n p} (g : C.[ n , p ]) (f : C.[ m , n ])
    → ι (g C.∘C f) ≡ (ι g) D.∘D (ι f)
  ι∘ [] f = refl
  ι∘ (r ∷ g) f = cong₂ _∷_ (𝕀[] r f) (ι∘ g f)

  F : Functor C.Cat D.Cat
  F .F-ob = idfun ℕ
  F .F-hom = ι
  F .F-id = idι _
  F .F-seq f g = ι∘ g f

{- Dedekind → De Morgan inclusion -}

module Dedekind→DeMorgan where

  private
    module D = Dedekind
    module M = DeMorgan

  𝕀 : ∀ {n} → D.𝕀 n → M.𝕀 n
  𝕀 = fst

  ι : ∀ {m n} → D.[ m , n ] → M.[ m , n ]
  ι = V.map 𝕀

  weak : ∀ {m n} (f : D.[ m , n ])
    → ι (D.weak f) ≡ M.weak (ι f)
  weak [] = refl
  weak (s ∷ f) = cong (_ ∷_) (weak f)

  idι : ∀ n → ι (D.idD n) ≡ M.idM n
  idι zero = refl
  idι (suc n) = cong (M.var ∷_) (weak (D.idD n) ∙ cong M.weak (idι n))

  ι∘ : ∀ {m n p} (g : D.[ n , p ]) (f : D.[ m , n ])
    → ι (g D.∘D f) ≡ (ι g) M.∘M (ι f)
  ι∘ [] f = refl
  ι∘ (r ∷ g) f = cong (_ ∷_) (ι∘ g f)

  F : Functor D.Cat M.Cat
  F .F-ob = idfun ℕ
  F .F-hom = ι
  F .F-id = idι _
  F .F-seq f g = ι∘ g f

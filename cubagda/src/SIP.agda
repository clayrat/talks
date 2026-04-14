{-# OPTIONS --safe #-}
module SIP where

open import Prelude
open import Meta.Effect

open import Data.Empty
open import Data.Reflects as Reflects
open import Data.Bool
open import Data.Nat
open import Data.List
open import Data.List.Operations.Properties

open import Algebra.Semigroup

open import Univalence
open import Bin

private variable
  ℓ ℓ′ ℓ″ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′
  C : 𝒰 ℓ″
  m n p : ℕ

-- we need ops too!

RawMonoidStructure : 𝒰 → 𝒰
RawMonoidStructure X = X × (X → X → X)

is-monoid : (M : 𝒰) → RawMonoidStructure M → 𝒰
is-monoid M (e , _·_) = is-semigroup _·_ × ((x : M) → (x · e ＝ x) × (e · x ＝ x))

monoid-desc : Desc 0ℓ 0ℓ RawMonoidStructure 0ℓ
monoid-desc .Desc.descriptor = auto-str-term!
monoid-desc .Desc.axioms = is-monoid
monoid-desc .Desc.axioms-prop X (e , op) M1 M2 =
  let sx = is-semigroup.has-is-of-hlevel (M1. fst) in
  prop! ,ₚ fun-ext λ x → sx _ _ _ _ ,ₚ sx _ _ _ _

monoid-str : Structure 0ℓ (desc→family monoid-desc)
monoid-str = desc→structure monoid-desc

@0 monoid-str-is-univalent : is-univalent monoid-str
monoid-str-is-univalent = desc→is-univalent monoid-desc

Monoid : 𝒰₁
Monoid = Type-with monoid-str

@0 Monoid-Path : {M N : Monoid} → (M ≃s[ monoid-str ] N) → (M ＝ N)
Monoid-Path = sip monoid-str-is-univalent

ℕ-is-semigroup : is-semigroup _+_
ℕ-is-semigroup .is-semigroup.has-magma .is-n-magma.has-is-of-hlevel = hlevel!
ℕ-is-semigroup .is-semigroup.assoc = +-assoc

ℕ-monoid : Monoid
ℕ-monoid .fst = ℕ
ℕ-monoid .snd = (0 , _+_) , ℕ-is-semigroup , λ x → +-zero-r x , refl

Bin-is-semigroup : is-semigroup binPlus
Bin-is-semigroup .is-semigroup.has-magma .is-n-magma.has-is-of-hlevel = hlevel!
Bin-is-semigroup .is-semigroup.assoc = add-assoc

Bin-monoid : Monoid
Bin-monoid .fst = Bin
Bin-monoid .snd = (BinO , binPlus) , Bin-is-semigroup , λ x → addZeroR x , addZeroL x

Conical : Monoid → 𝒰
Conical (T , (e , op) , m) = (x y : T) → op x y ＝ e → (x ＝ e) × (y ＝ e)

ℕ-Conical : Conical ℕ-monoid
ℕ-Conical  zero    zero   e = refl , refl
ℕ-Conical  zero   (suc y) e = false! e
ℕ-Conical (suc x)  y      e = false! e

@0 ℕ＝Bin : ℕ-monoid ＝ Bin-monoid
ℕ＝Bin = Monoid-Path (ℕ≃Bin , refl , ℕ→Bin-+)

@0 Bin-Conical : Conical Bin-monoid
Bin-Conical = subst Conical ℕ＝Bin ℕ-Conical

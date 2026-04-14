{-# OPTIONS --safe #-}
module Bin where

open import Prelude
open import Data.Bool
open import Data.Reflects.Base as Reflects
open import Data.Nat

open import Bip public

-- Natural binary number
data Bin : 𝒰 where
  BinO : Bin
  BinP : Bip → Bin

private variable
  a b : Bin
  p q : Bip

BinP-inj : BinP p ＝ BinP q → p ＝ q
BinP-inj {p} {q} = ap go where
  go : Bin → Bip
  go (BinP x) = x
  go  BinO    = U

is-zero : Bin → Bool
is-zero  BinO    = true
is-zero (BinP _) = false

_==ᵇ-bin_ : Bin → Bin → Bool
BinO   ==ᵇ-bin BinO   = true
BinP a ==ᵇ-bin BinP b = a ==ᵇ b
BinO   ==ᵇ-bin BinP _ = false
BinP _ ==ᵇ-bin BinO   = false

instance
  Reflects-BinP : {bl : Bool} → ⦃ Reflects (p ＝ q) bl ⦄ → Reflects (BinP p ＝ BinP q) bl
  Reflects-BinP = Reflects.dmap (ap BinP) (⊥.contra BinP-inj) auto
  {-# INCOHERENT Reflects-BinP #-}

  Reflects-Bin-Path : Reflects (a ＝ b) (a ==ᵇ-bin b)
  Reflects-Bin-Path {a = BinO}   {b = BinO}   = ofʸ refl
  Reflects-Bin-Path {a = BinO}   {b = BinP _} = ofⁿ (λ e → false! (ap is-zero e))
  Reflects-Bin-Path {a = BinP _} {b = BinO}   = ofⁿ (λ e → false! (ap is-zero e))
  Reflects-Bin-Path {a = BinP p} {b = BinP q} = Reflects.dmap
                                                  (ap BinP)
                                                  (⊥.contra BinP-inj)
                                                  (Reflects-Bip-Path {p} {q})

  Bin-is-discrete : is-discrete Bin
  Bin-is-discrete = reflects-path→is-discrete!

Bin-identity-system : is-identity-system (λ a b → ⌞ a ==ᵇ-bin b ⌟) _
Bin-identity-system = reflects-path→identity-system!

instance opaque
  H-Level-Bin : ∀ {k} → H-Level (2 + k) Bin
  H-Level-Bin = hlevel-basic-instance 2 $
    identity-system→is-of-hlevel! 1 Bin-identity-system
  {-# OVERLAPPING H-Level-Bin #-}

-- Successor
binSucc : Bin → Bin
binSucc  BinO    = BinP U
binSucc (BinP a) = BinP (bipSucc a)

-- Addition on Bin
binPlus : Bin → Bin → Bin
binPlus  BinO     BinO    = BinO
binPlus  BinO    (BinP b) = BinP b
binPlus (BinP a)  BinO    = BinP a
binPlus (BinP a) (BinP b) = BinP (bipPlus a b)

addZeroL : (a : Bin) → binPlus BinO a ＝ a
addZeroL  BinO    = refl
addZeroL (BinP _) = refl

addZeroR : (a : Bin) → binPlus a BinO ＝ a
addZeroR  BinO    = refl
addZeroR (BinP _) = refl

bin-addSuccL : (a b : Bin) → binPlus (binSucc a) b ＝ binSucc (binPlus a b)
bin-addSuccL  BinO     BinO    = refl
bin-addSuccL  BinO    (BinP b) = ap BinP (add1L b)
bin-addSuccL (BinP _)  BinO    = refl
bin-addSuccL (BinP a) (BinP b) = ap BinP (addSuccL a b)

-- Commutativity for Bin
add-comm : (a b : Bin) → binPlus a b ＝ binPlus b a
add-comm  BinO     BinO    = refl
add-comm  BinO    (BinP _) = refl
add-comm (BinP _)  BinO    = refl
add-comm (BinP a) (BinP b) = ap BinP (addComm a b)

bin-addSuccR : (a b : Bin) → binPlus a (binSucc b) ＝ binSucc (binPlus a b)
bin-addSuccR a b = add-comm a (binSucc b) ∙ bin-addSuccL b a ∙ ap binSucc (add-comm b a)

-- Associativity for Bin
add-assoc : (a b c : Bin) → binPlus a (binPlus b c) ＝ binPlus (binPlus a b) c
add-assoc  BinO     BinO     BinO    = refl
add-assoc  BinO     BinO    (BinP _) = refl
add-assoc  BinO    (BinP _)  BinO    = refl
add-assoc  BinO    (BinP _) (BinP _) = refl
add-assoc (BinP _)  BinO     BinO    = refl
add-assoc (BinP _)  BinO    (BinP _) = refl
add-assoc (BinP _) (BinP _)  BinO    = refl
add-assoc (BinP a) (BinP b) (BinP c) = ap BinP (addAssoc a b c)

-- ℕ conversion

Bin→ℕ : Bin → ℕ
Bin→ℕ  BinO    = zero
Bin→ℕ (BinP x) = Bip→ℕ x

ℕ→Bin : ℕ → Bin
ℕ→Bin  zero   = BinO
ℕ→Bin (suc n) = binSucc (ℕ→Bin n)

-- homomorphism!
ℕ→Bin-+ : (m n : ℕ) → ℕ→Bin (m + n) ＝ binPlus (ℕ→Bin m) (ℕ→Bin n)
ℕ→Bin-+  zero n   = addZeroL (ℕ→Bin n) ⁻¹
ℕ→Bin-+ (suc m) n = ap binSucc (ℕ→Bin-+ m n) ∙ bin-addSuccL (ℕ→Bin m) (ℕ→Bin n) ⁻¹

bin→ℕ-suc : (b : Bin) → Bin→ℕ (binSucc b) ＝ suc (Bin→ℕ b)
bin→ℕ-suc  BinO    = refl
bin→ℕ-suc (BinP b) = bip→ℕ-suc b

ℕ→Bin-Bip→ℕ : (b : Bip) → ℕ→Bin (Bip→ℕ b) ＝ BinP b
ℕ→Bin-Bip→ℕ  U     = refl
ℕ→Bin-Bip→ℕ (xO b) =
    ap (λ q → ℕ→Bin (Bip→ℕ b + q)) (+-zero-r (Bip→ℕ b))
  ∙ ℕ→Bin-+ (Bip→ℕ b) (Bip→ℕ b)
  ∙ ap (λ q → binPlus q q) (ℕ→Bin-Bip→ℕ b)
  ∙ ap BinP (addDiag b)  
ℕ→Bin-Bip→ℕ (xI b) =
    ap binSucc (  ap (λ q → ℕ→Bin (Bip→ℕ b + q)) (+-zero-r (Bip→ℕ b))
                ∙ ℕ→Bin-+ (Bip→ℕ b) (Bip→ℕ b)
                ∙ ap (λ q → binPlus q q) (ℕ→Bin-Bip→ℕ b))
  ∙ ap (BinP ∘ bipSucc) (addDiag b)

ℕ→Bin→ℕ : (b : Bin) → ℕ→Bin (Bin→ℕ b) ＝ b
ℕ→Bin→ℕ  BinO    = refl
ℕ→Bin→ℕ (BinP x) = ℕ→Bin-Bip→ℕ x

Bin→ℕ→Bin : (n : ℕ) → Bin→ℕ (ℕ→Bin n) ＝ n
Bin→ℕ→Bin  zero   = refl
Bin→ℕ→Bin (suc n) = bin→ℕ-suc (ℕ→Bin n) ∙ ap suc (Bin→ℕ→Bin n)

ℕ≃Bin : ℕ ≃ Bin
ℕ≃Bin =
  ≅→≃ $
  make-iso ℕ→Bin Bin→ℕ $
  make-inverses (fun-ext ℕ→Bin→ℕ) (fun-ext Bin→ℕ→Bin)

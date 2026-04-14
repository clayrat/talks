{-# OPTIONS --safe #-}
module Bip where

open import Prelude
open import Data.Bool
open import Data.Reflects.Base as Reflects
open import Data.Nat

-- Positive binary number, little endian
data Bip : 𝒰 where
  U  : Bip
  xO : Bip → Bip
  xI : Bip → Bip

private variable
  p q : Bip

div2 : Bip → Bip
div2  U     = U
div2 (xO x) = x
div2 (xI x) = x

xO-inj : xO p ＝ xO q → p ＝ q
xO-inj = ap div2

xI-inj : xI p ＝ xI q → p ＝ q
xI-inj = ap div2

_==ᵇ_ : Bip → Bip → Bool
U    ==ᵇ U    = true
xO a ==ᵇ xO b = a ==ᵇ b
xI a ==ᵇ xI b = a ==ᵇ b
U    ==ᵇ xO _ = false
U    ==ᵇ xI _ = false
xO _ ==ᵇ U    = false
xO _ ==ᵇ xI _ = false
xI _ ==ᵇ U    = false
xI _ ==ᵇ xO _ = false

bip-discrim : Bip → ℕ
bip-discrim  U     = 0
bip-discrim (xO _) = 1
bip-discrim (xI _) = 2

instance
  Reflects-xO : {b : Bool} → ⦃ Reflects (p ＝ q) b ⦄ → Reflects (xO p ＝ xO q) b
  Reflects-xO = Reflects.dmap (ap xO) (⊥.contra xO-inj) auto
  {-# INCOHERENT Reflects-xO #-}

  Reflects-xI : {b : Bool} → ⦃ Reflects (p ＝ q) b ⦄ → Reflects (xI p ＝ xI q) b
  Reflects-xI = Reflects.dmap (ap xI) (⊥.contra xI-inj) auto
  {-# INCOHERENT Reflects-xI #-}

  Reflects-Bip-Path : Reflects (p ＝ q) (p ==ᵇ q)
  Reflects-Bip-Path {p = U}    {q = U}    = ofʸ refl
  Reflects-Bip-Path {p = U}    {q = xO _} = ofⁿ (λ e → false! (ap bip-discrim e))
  Reflects-Bip-Path {p = U}    {q = xI _} = ofⁿ (λ e → false! (ap bip-discrim e))
  Reflects-Bip-Path {p = xO _} {q = U}    = ofⁿ (λ e → false! (ap bip-discrim e))
  Reflects-Bip-Path {p = xO p} {q = xO q} = Reflects.dmap (ap xO) (⊥.contra xO-inj) (Reflects-Bip-Path {p} {q})
  Reflects-Bip-Path {p = xO _} {q = xI _} = ofⁿ (λ e → false! (ap bip-discrim e))
  Reflects-Bip-Path {p = xI _} {q = U}    = ofⁿ (λ e → false! (ap bip-discrim e))
  Reflects-Bip-Path {p = xI _} {q = xO _} = ofⁿ (λ e → false! (ap bip-discrim e))
  Reflects-Bip-Path {p = xI p} {q = xI q} = Reflects.dmap (ap xI) (⊥.contra xI-inj) (Reflects-Bip-Path {p} {q})

  Bip-is-discrete : is-discrete Bip
  Bip-is-discrete = reflects-path→is-discrete!

Bip-identity-system : is-identity-system (λ p q → ⌞ p ==ᵇ q ⌟) _
Bip-identity-system = reflects-path→identity-system!

instance opaque
  H-Level-Bip : ∀ {k} → H-Level (2 + k) Bip
  H-Level-Bip = hlevel-basic-instance 2 $
    identity-system→is-of-hlevel! 1 Bip-identity-system
  {-# OVERLAPPING H-Level-Bip #-}

-- Successor
bipSucc : Bip → Bip
bipSucc  U     = xO U
bipSucc (xO a) = xI a
bipSucc (xI a) = xO (bipSucc a)

-- Addition and carry
mutual
  bipPlus : Bip → Bip → Bip
  bipPlus  U      U     = xO U
  bipPlus  U     (xO b) = xI b
  bipPlus  U     (xI b) = xO (bipSucc b)
  bipPlus (xO a)  U     = xI a
  bipPlus (xO a) (xO b) = xO (bipPlus a b)
  bipPlus (xO a) (xI b) = xI (bipPlus a b)
  bipPlus (xI a)  U     = xO (bipSucc a)
  bipPlus (xI a) (xO b) = xI (bipPlus a b)
  bipPlus (xI a) (xI b) = xO (bipCarry a b)

  bipCarry : Bip → Bip → Bip
  bipCarry  U      U     = xI U
  bipCarry  U     (xO b) = xO (bipSucc b)
  bipCarry  U     (xI b) = xI (bipSucc b)
  bipCarry (xO a)  U     = xO (bipSucc a)
  bipCarry (xO a) (xO b) = xI (bipPlus a b)
  bipCarry (xO a) (xI b) = xO (bipCarry a b)
  bipCarry (xI a)  U     = xI (bipSucc a)
  bipCarry (xI a) (xO b) = xO (bipCarry a b)
  bipCarry (xI a) (xI b) = xI (bipCarry a b)

-- Lemmas

add1R : (p : Bip) → bipPlus p U ＝ bipSucc p
add1R  U     = refl
add1R (xO _) = refl
add1R (xI _) = refl

add1L : (p : Bip) → bipPlus U p ＝ bipSucc p
add1L  U     = refl
add1L (xO _) = refl
add1L (xI _) = refl

addCarrySpec : (p q : Bip) → bipCarry p q ＝ bipSucc (bipPlus p q)
addCarrySpec  U      U     = refl
addCarrySpec  U     (xO _) = refl
addCarrySpec  U     (xI _) = refl
addCarrySpec (xO _)  U     = refl
addCarrySpec (xO _) (xO _) = refl
addCarrySpec (xO a) (xI b) = ap xO (addCarrySpec a b)
addCarrySpec (xI _)  U     = refl
addCarrySpec (xI a) (xO b) = ap xO (addCarrySpec a b)
addCarrySpec (xI _) (xI _) = refl

-- Commutativity
addComm : (p q : Bip) → bipPlus p q ＝ bipPlus q p
addComm  U      q     = add1L q ∙ add1R q ⁻¹
addComm (xO a)  U     = add1R (xO a) ∙ add1L (xO a) ⁻¹
addComm (xI a)  U     = add1R (xI a) ∙ add1L (xI a) ⁻¹
addComm (xO a) (xO b) = ap xO (addComm a b)
addComm (xO a) (xI b) = ap xI (addComm a b)
addComm (xI a) (xO b) = ap xI (addComm a b)
addComm (xI a) (xI b) = ap xO (addCarrySpec a b ∙ ap bipSucc (addComm a b) ∙ addCarrySpec b a ⁻¹)

addSuccR : (p q : Bip) → bipPlus p (bipSucc q) ＝ bipSucc (bipPlus p q)
addSuccR  U      q     = add1L (bipSucc q) ∙ ap bipSucc (add1L q) ⁻¹
addSuccR (xO a)  U     = ap xO (add1R a)
addSuccR (xI a)  U     = ap xI (add1R a)
addSuccR (xO _) (xO _) = refl
addSuccR (xO a) (xI b) = ap xO (addSuccR a b)
addSuccR (xI a) (xO b) = ap xO (addCarrySpec a b)
addSuccR (xI a) (xI b) = ap xI (addSuccR a b ∙ addCarrySpec a b ⁻¹)

addSuccL : (p q : Bip) → bipPlus (bipSucc p) q ＝ bipSucc (bipPlus p q)
addSuccL p q = addComm (bipSucc p) q ∙ addSuccR q p ∙ ap bipSucc (addComm q p)

-- Associativity
addAssoc : (p q r : Bip) → bipPlus p (bipPlus q r) ＝ bipPlus (bipPlus p q) r
addAssoc  U      q      r     =   add1L (bipPlus q r)
                                ∙ addSuccL q r ⁻¹
                                ∙ ap (λ z → bipPlus z r) (add1L q ⁻¹)
addAssoc (xO a)  U      r     =   ap (bipPlus (xO a)) (add1L r)
                                ∙ addSuccR (xO a) r
                                ∙ addSuccL (xO a) r ⁻¹
addAssoc (xI a)  U      r     =   ap (bipPlus (xI a)) (add1L r)
                                ∙ addSuccR (xI a) r
                                ∙ addSuccL (xI a) r ⁻¹
addAssoc (xO a) (xO b)  U     = refl
addAssoc (xO a) (xI b)  U     = ap xO (addSuccR a b)
addAssoc (xI a) (xO b)  U     = ap xO (addCarrySpec a b)
addAssoc (xI a) (xI b)  U     = ap xI (addSuccR a b ∙ addCarrySpec a b ⁻¹)
addAssoc (xO a) (xO b) (xO c) = ap xO (addAssoc a b c)
addAssoc (xO a) (xO b) (xI c) = ap xI (addAssoc a b c)
addAssoc (xO a) (xI b) (xO c) = ap xI (addAssoc a b c)
addAssoc (xO a) (xI b) (xI c) = ap xO (  ap (bipPlus a) (addCarrySpec b c)
                                       ∙ addSuccR a (bipPlus b c)
                                       ∙ ap bipSucc (addAssoc a b c)
                                       ∙ addCarrySpec (bipPlus a b) c ⁻¹)
addAssoc (xI a) (xO b) (xO c) = ap xI (addAssoc a b c)
addAssoc (xI a) (xO b) (xI c) = ap xO (  addCarrySpec a (bipPlus b c)
                                       ∙ ap bipSucc (addAssoc a b c)
                                       ∙ addCarrySpec (bipPlus a b) c ⁻¹)
addAssoc (xI a) (xI b) (xO c) = ap xO (  addCarrySpec a (bipPlus b c)
                                       ∙ ap bipSucc (addAssoc a b c)
                                       ∙ addSuccL (bipPlus a b) c ⁻¹
                                       ∙ ap (λ z → bipPlus z c) (addCarrySpec a b ⁻¹))
addAssoc (xI a) (xI b) (xI c) = ap xI (  ap (bipPlus a) (addCarrySpec b c)
                                       ∙ addSuccR a (bipPlus b c)
                                       ∙ ap bipSucc (addAssoc a b c)
                                       ∙ addSuccL (bipPlus a b) c ⁻¹
                                       ∙ ap (λ z → bipPlus z c) (addCarrySpec a b ⁻¹))

addDiag : (p : Bip) → bipPlus p p ＝ xO p
addDiag  U     = refl
addDiag (xO a) = ap xO (addDiag a)
addDiag (xI a) = ap xO (addCarrySpec a a ∙ ap bipSucc (addDiag a))

-- ℕ conversion

Bip→ℕ : Bip → ℕ
Bip→ℕ  U     = 1
Bip→ℕ (xO x) = 2 · Bip→ℕ x 
Bip→ℕ (xI x) = suc (2 · Bip→ℕ x)

bip→ℕ-suc : (b : Bip) → Bip→ℕ (bipSucc b) ＝ suc (Bip→ℕ b)
bip→ℕ-suc  U     = refl
bip→ℕ-suc (xO b) = refl
bip→ℕ-suc (xI b) = ap (2 ·_) (bip→ℕ-suc b) ∙ ap suc (+-suc-r _ _)

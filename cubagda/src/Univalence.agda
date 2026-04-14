{-# OPTIONS --safe #-}
module Univalence where

open import Prelude
open import Meta.Effect

open import Data.Empty
open import Data.Bool as Bool
open import Data.Reflects as Reflects
open import Data.Dec
open import Data.Nat
open import Data.Fin.Inductive
open import Data.Fin.Inductive.Operations
open import Data.List
open import Data.List.Operations.Properties
open import Data.Vec.Inductive

open import Bin

private variable
  ℓ ℓ′ ℓ″ : Level
  n : ℕ

not-inv : (x : Bool) → not (not x) ＝ x
not-inv true  = refl
not-inv false = refl

twistₑ : Bool ≃ Bool
twistₑ = ≅→≃ $ make-iso not not $
         make-inverses
           (fun-ext not-inv)
           (fun-ext not-inv)

@0 twist : Bool ＝ Bool
twist = ua twistₑ

@0 uafalse : transport twist false ＝ true
uafalse = ua-β twistₑ false

@0 foo : false ＝ false
foo = refl
    ua-β twistₑ true ⁻¹
  ∙ ap (transport twist) (the (true ＝ true) refl)
  ∙ ua-β twistₑ true

-- Bool has only 2 symmetries
@0 only-two : Fin 2 ≃ Bool ＝ Bool
only-two =  ≅→≃ $ make-iso f g $
        make-inverses
          (fun-ext re)
          (fun-ext se)
  where
  f : Fin 2 → Bool ＝ Bool
  f       fzero  = refl
  f (fsuc fzero) = twist

  g : Bool ＝ Bool → Fin 2
  g e = if transport e true then fzero else fsuc fzero

  re : (e : Bool ＝ Bool)
     → f (g e) ＝ e
  re e with transport e true ≟ true | transport e false ≟ false
  re e | yes pt | yes pf =
      ap (λ q → f (if q then fzero else fsuc fzero)) pt
    ∙ ua-η refl ⁻¹
    ∙ ap ua (=→≃-refl ∙ ext (Bool.elim (pt ⁻¹) (pf ⁻¹)))
    ∙ ua-η e
  re e | yes pt | no ¬pf =
    false! (is-embedding→injective (is-equiv→is-embedding (transport-is-equiv e))
              (pt ∙ ≠→=not _ _ ¬pf ⁻¹))
  re e | no ¬pt | yes pf =
    false! (is-embedding→injective (is-equiv→is-embedding (transport-is-equiv e))
              (pf ∙ ≠→=not _ _ ¬pt ⁻¹))
  re e | no ¬pt | no ¬pf =
    let ptf = ≠→=not _ _ ¬pt
        pft = ≠→=not _ _ ¬pf
      in
      ap (λ q → f (if q then fzero else fsuc fzero)) ptf
    ∙ ap ua (ext (Bool.elim (ptf ⁻¹) (pft ⁻¹)))
    ∙ ua-η e
    
  se : (x : Fin 2)
     → g (f x) ＝ x
  se  fzero       = refl
  se (fsuc fzero) = ap (λ q → if q then fzero else fsuc fzero) (ua-β twistₑ true)

-- Nat/Bin

data IsEven : ℕ → 𝒰 where
  EZ  : IsEven zero
  ESS : ∀ {n} → IsEven n → IsEven (suc (suc n))


data IsEvenP : Bip → 𝒰 where
  E2 : IsEvenP (xO U)
  ExO : ∀ {n} → IsEvenP n → IsEvenP (xO n)

data IsEvenN : Bin → 𝒰 where
  EO : IsEvenN BinO
  EP : ∀ {n} → IsEvenP n → IsEvenN (BinP n)


-- transported
@0 IsEvenN' : Bin → 𝒰
IsEvenN' = subst (λ q → q → 𝒰) (ua ℕ≃Bin) IsEven

{-
is-even : ℕ → Bool
is-even zero = true
is-even (suc zero) = false
is-even (suc (suc n)) = is-even n

is-even-reflects : Reflects (fibre (2 ·_) n) (is-even n)
is-even-reflects {n = zero} = ofʸ (0 , refl)
is-even-reflects {n = suc zero} =
  ofⁿ (λ where
           (zero , e) → false! e
           (suc x , e) → false! (+-suc-r x (x + 0) ⁻¹ ∙ suc-inj e))
is-even-reflects {n = suc (suc n)} =
  Reflects.dmap
    (λ where (x , e) → suc x , ap suc (+-suc-r x (x + 0) ∙ ap suc e))
    (contra λ where
                (zero , e) → false! e
                (suc x , e) → x , suc-inj (+-suc-r x (x + 0) ⁻¹ ∙ suc-inj e))
    (is-even-reflects {n = n})
-}

module Theories.SO.PSOGAT where

open import Data.Product using (proj₁; proj₂; _,_; _×_)
open import Utils hiding (⊤; _∧_)
open import Theories.Phase public
open import Theories.SO.GAT
open import Theories.SO.SOGAT

module in-SOGAT (Φ : PhaseAlg) (sogat : SOGAT-ToS) where
  open PhaseAlg Φ
  open SOGAT-ToS sogat

  variable
    t u v : Phase
    A B : Ty
    a : Tm A
    F : Tm A → Ty
    f : Tm A → Tm B

  record PSOGAT-ToSᶜ : Set₁ where
    field
      In : Phase → Ty
      In-prop : (x y : Tm (In t)) → x ≡ y
      in⊤ : Tm (In ⊤)
      In-and-proj : (Tm (In t) × Tm (In u)) ≃ Tm (In (t ∧ u))

      -- Open modality for all sorts

      Πᴾ : (t : Phase) (F : Tm (In t) → Ty) → Ty
      ↓↑ : ((x : Tm (In t)) → Tm (F x)) ≃ Tm (Πᴾ t F)

      Πᴾᵁ : (t : Phase) (f : Tm (In t) → Tm U) → Tm U
      ↓↑ᵁ : ((x : Tm (In t)) → Tm (El (f x))) ≃ Tm (El (Πᴾᵁ t f))

      Πᴾᴿ : (t : Phase) (f : Tm (In t) → Tm Uᴿ) → Tm Uᴿ
      ↓↑ᴿ : ((x : Tm (In t)) → Tm (El (elᴿ (f x)))) ≃ Tm (El (elᴿ (Πᴾᴿ t f)))

    In-and : Tm (In t) → Tm (In u) → Tm (In (t ∧ u))
    In-and x y = In-and-proj .to (x , y)

    In-fst : Tm (In (t ∧ u)) → Tm (In t)
    In-fst z = In-and-proj .from z .proj₁

    In-snd : Tm (In (t ∧ u)) → Tm (In u)
    In-snd z = In-and-proj .from z .proj₂

record PSOGAT-ToS (Φ : PhaseAlg) : Set₁ where
  field
    sogat : SOGAT-ToS
  open SOGAT-ToS sogat public
  field
    psogat-ctors : in-SOGAT.PSOGAT-ToSᶜ Φ sogat
  open in-SOGAT.PSOGAT-ToSᶜ psogat-ctors public

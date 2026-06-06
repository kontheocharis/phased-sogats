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
    A : Ty
    a : Tm A

  record PSOGAT-ToSᶜ : Set₁ where
    field
      In : Phase → Ty
      In-prop : (x y : Tm (In t)) → x ≡ y
      in⊤ : Tm (In ⊤)
      In-and-proj : (Tm (In t) × Tm (In u)) ≃ Tm (In (t ∧ u))

      Πᴾ : (p : Phase) → Tm U → Tm U
      Πᴾᴿ : (p : Phase) → Tm Uᴿ → Tm Uᴿ
      ↓↑ : (Tm (In t) → Tm (El a)) ≃ Tm (El (Πᴾ t a))
      ↓↑ᴿ : (Tm (In t) → Tm (El (elᴿ a))) ≃ Tm (El (elᴿ (Πᴾᴿ t a)))

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

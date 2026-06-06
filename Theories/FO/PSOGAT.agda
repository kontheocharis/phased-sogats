module Theories.FO.PSOGAT where

open import Utils hiding (⊤; _∧_)
open import Theories.Phase public
open import Theories.FO.CwF
open import Theories.FO.GAT
open import Theories.FO.SOGAT
open import Data.Product using (_×_)

module InSOGAT (Φ : PhaseAlg) (sogat : SOGAT-ToS) where
  open PhaseAlg Φ
  open SOGAT-ToS sogat

  variable
    t u v : Phase
    Au Bu : Tm Γ U
    AuR BuR : Tm Γ Uᴿ

  record PSOGATCtors : Set₁ where
    field
      In : Phase → Ty Γ
      In[] : (In {Γ = Δ} t) [ σ ]T ≡ In t
      In-prop : (x y : Tm Γ (In t)) → x ≡ y
      in⊤ : Tm Γ (In ⊤)
      in-and-proj : (Tm Γ (In t) × Tm Γ (In u)) ≃ Tm Γ (In (t ∧ u))

      -- Open modality for all sorts

      Πᴾ : (t : Phase) → Ty (Γ ▷ In t) → Ty Γ
      ↑↓ : Tm (Γ ▷ In t) A ≃ Tm Γ (Πᴾ t A)
      -- @@Todo: substitution

      Πᴾᵁ : (t : Phase) → Tm (Γ ▷ In t) U → Tm Γ U
      ↑↓ᵁ : Tm (Γ ▷ In t) (El Au) ≃ Tm Γ (El (Πᴾᵁ t Au))
      -- @@Todo: substitution

      Πᴾᴿ : (t : Phase) → Tm (Γ ▷ In t) Uᴿ → Tm Γ Uᴿ
      ↑↓ᴿ : Tm (Γ ▷ In t) (El (elᴿ AuR)) ≃ Tm Γ (El (elᴿ (Πᴾᴿ t AuR)))
      -- @@Todo: substitution

record PSOGAT-ToS (Φ : PhaseAlg) : Set₁ where
  field
    sogat : SOGAT-ToS
  open SOGAT-ToS sogat public
  field
    psogat-ctors : InSOGAT.PSOGATCtors Φ sogat
  open InSOGAT.PSOGATCtors psogat-ctors public

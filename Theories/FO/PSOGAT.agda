module Theories.FO.PSOGAT where

open import Utils hiding (⊤; _∧_)
open import Theories.FO.CwF
open import Theories.FO.GAT
open import Theories.FO.SOGAT

private variable
  X : Set
  t u v : X

record PhaseAlg : Set₁ where
  field
    Phase : Set
    _∧_ : Phase → Phase → Phase
    ⊤ : Phase
    ∧assoc : (t ∧ u) ∧ v ≡ t ∧ (u ∧ v)
    ∧comm : t ∧ u ≡ u ∧ t
    ∧idemp : t ∧ t ≡ t
    ∧⊤ : t ∧ ⊤ ≡ t

module InSOGAT (Φ : PhaseAlg) (sogat : SOGAT-ToS) where
  open PhaseAlg Φ
  open SOGAT-ToS sogat

  variable
    Au Bu : Tm Γ U
    AuR BuR : Tm Γ Uᴿ

  record PSOGATCtors : Set₁ where
    field
      In : Phase → Ty Γ
      In[] : (In {Γ = Δ} t) [ σ ]T ≡ In t
      In-prop : (x y : Tm Γ (In t)) → x ≡ y
      in⊤ : Tm Γ (In ⊤)
      in-and : Tm Γ (In t) → Tm Γ (In u) → Tm Γ (In (t ∧ u))
      in-fst : Tm Γ (In (t ∧ u)) → Tm Γ (In t)
      in-snd : Tm Γ (In (t ∧ u)) → Tm Γ (In u)

      -- Open modality for U
      Πᴾ : Phase → Tm Γ U → Tm Γ U
      ↑ : Tm (Γ ▷ In t) ((El Au) [ p ]T) → Tm Γ (El (Πᴾ t Au))
      ↓ : Tm Γ (El (Πᴾ t Au)) → Tm (Γ ▷ In t) (El Au [ p ]T)
      ↓↑ : ↓ (↑ a) ≡ a
      ↑↓ : ↑ (↓ a) ≡ a

      -- Open modality for UR
      Πᴾᴿ : Phase → Tm Γ Uᴿ → Tm Γ Uᴿ
      ↑ᴿ : Tm (Γ ▷ In t) (El (elᴿ AuR) [ p ]T) → Tm Γ (El (elᴿ (Πᴾᴿ t AuR)))
      ↓ᴿ : Tm Γ (El (elᴿ (Πᴾᴿ t AuR))) → Tm (Γ ▷ In t) (El (elᴿ AuR) [ p ]T)
      ↓↑ᴿ : ↓ᴿ (↑ᴿ a) ≡ a
      ↑↓ᴿ : ↑ᴿ (↓ᴿ a) ≡ a

record PSOGAT-ToS (Φ : PhaseAlg) : Set₁ where
  field
    sogat : SOGAT-ToS
  open SOGAT-ToS sogat public
  field
    psogat-ctors : InSOGAT.PSOGATCtors Φ sogat
  open InSOGAT.PSOGATCtors psogat-ctors public

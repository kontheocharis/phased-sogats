module Theories.FO.PSOGAT where

open import Utils hiding (⊤; _∧_)
open import Theories.Phase public
open import Theories.FO.CwF
open import Theories.FO.GAT
open import Theories.FO.SOGAT

module InSOGAT (Φ : PhaseAlg) (sogat : SOGAT-ToS) where
  open PhaseAlg Φ
  open SOGAT-ToS sogat

  variable
    t u v : Phase
    Au Bu : Tm Γ U
    AuR BuR : Tm Γ Uᴿ

  record PSOGATSorts : Set₁ where
    field
      In : Con → Phase → Set
      In-prop : (π π' : In Γ t) → π ≡ π'

  module InPSOGATSorts (psorts : PSOGATSorts) where
    open PSOGATSorts psorts

    variable
      π π' : In Γ t

    record PSOGATCtors : Set₁ where
      field
        _[_]ᴵ : In Δ t → Sub Γ Δ → In Γ t
        _▷ᴵ_ : Con → Phase → Con
        pᴵ : Sub (Γ ▷ᴵ t) Γ
        qᴵ : In (Γ ▷ᴵ t) t
        _,ᴵ_ : (σ : Sub Γ Δ) → In Γ t → Sub Γ (Δ ▷ᴵ t)
        ,ᴵ∘ : (σ ,ᴵ π) ∘ τ ≡ (σ ∘ τ) ,ᴵ (π [ τ ]ᴵ)
        p,ᴵq : pᴵ {Γ} {t} ,ᴵ qᴵ ≡ id
        pᴵ∘,ᴵ : pᴵ ∘ (σ ,ᴵ π) ≡ σ

        Πᴾ : (t : Phase) → Ty (Γ ▷ᴵ t) → Ty Γ
        ↑↓ : Tm (Γ ▷ᴵ t) A ≃ Tm Γ (Πᴾ t A)
        Πᴾᵁ : (t : Phase) → Tm (Γ ▷ᴵ t) U → Tm Γ U
        ↑↓ᵁ : Tm (Γ ▷ᴵ t) (El Au) ≃ Tm Γ (El (Πᴾᵁ t Au))
        Πᴾᴿ : (t : Phase) → Tm (Γ ▷ᴵ t) Uᴿ → Tm Γ Uᴿ
        ↑↓ᴿ : Tm (Γ ▷ᴵ t) (El (elᴿ AuR)) ≃ Tm Γ (El (elᴿ (Πᴾᴿ t AuR)))

      _⁺ᴵ : (σ : Sub Γ Δ) → Sub (Γ ▷ᴵ t) (Δ ▷ᴵ t)
      σ ⁺ᴵ = (σ ∘ pᴵ) ,ᴵ qᴵ

record PSOGAT-ToS (Φ : PhaseAlg) : Set₂ where
  field
    sogat : SOGAT-ToS
  open SOGAT-ToS sogat public
  field
    psogat-sorts : InSOGAT.PSOGATSorts Φ sogat
  open InSOGAT.PSOGATSorts psogat-sorts public
  field
    psogat-ctors : InSOGAT.InPSOGATSorts.PSOGATCtors Φ sogat psogat-sorts
  open InSOGAT.InPSOGATSorts.PSOGATCtors psogat-ctors public

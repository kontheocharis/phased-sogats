module Translation.PSOGAT-to-SOGAT where

open import Theories.Phase
import Theories.SO.SOGAT as SO
import Theories.FO.CwF as FO-CwF
import Theories.FO.GAT as FO-GAT
import Theories.FO.SOGAT as FO-SOGAT
import Theories.FO.PSOGAT as FO
open import Utils hiding (⊤; _∧_)
open import Data.Unit using (tt) renaming (⊤ to 𝟙)
open import Data.Product using (Σ-syntax; proj₁; proj₂) renaming (_,_ to _,,_)

module PSOGAT-to-SOGAT (Φ : PhaseAlg) (s : SO.In-SOGAT-ToS) where
  -- Here we enter the internal language of Psh(SOGAT-ToS). In other
  -- words a two-level type theory where the object language is the SOGAT ToS.
  open SO.SOGAT-ToS s
  open InPhaseAlg Φ

  module _
    (# : Phase → Tm Uᴿ)
    (#-map : ∀ {p q} → q ≤ p → Tm (El (Πᴿ (# q) (λ _ → elᴿ (# p)))))
    where

    module P = FO.PSOGAT-ToS
    module S = FO-SOGAT.SOGAT-ToS
    module G = FO-GAT.GAT-ToS
    module C = FO-CwF.CwF
    module Cˢ = FO-CwF.CwFSorts
    module Cᶜ = FO-CwF.InCwFSorts.CwFCtors
    module Gᶜ = FO-GAT.InCwF.GATCtors
    module Sᶜ = FO-SOGAT.InGAT.SOGATCtors
    module Pˢ = FO.InSOGAT.PSOGATSorts
    module Pᶜ = FO.InSOGAT.InPSOGATSorts.PSOGATCtors

    variable
      le : q ≤ p
      le' : r ≤ q

    Conᴹ : Set
    Conᴹ = Tm U

    variable
      Γ Δ Θ : Conᴹ
      γ : Tm (El Γ)

    Subᴹ : (Γ Δ : Conᴹ) → Set
    Subᴹ Γ Δ = Tm (El Γ) → Tm (El Δ)

    tyᴹ : (Γ : Conᴹ) → Ty
    tyᴹ Γ = Γ ⇒ U

    tyᴹᴿ : (Γ : Conᴹ) → Ty
    tyᴹᴿ Γ =
      X ∶ [ p ∶ Phase ] ⇒ᴱ [ γ ∶ # p ⇒ᴿ Γ ] ⇒ Uᴿ ⨾
      ↓↑ ∶ [ p ∶ Phase ] ⇒ᴱ ([ γ ∶ # p ⇒ᴿ Γ ]
        ⇒ Iso
          ([ i ∶ # p ] ⇒ᴿ elᴿ ((X ∙ᴱ ⊤) ∙ lamᴿ λ _ → γ ∙ᴿ i))
          (elᴿ ((X ∙ᴱ p) ∙ γ))) ⨾
      `1

    _＠_ : Tm (tyᴹᴿ Γ) → (p : Phase) → (γ : Tm (El (# p ⇒ᴿ Γ))) → Tm Uᴿ
    (A ＠ p) γ = (first A ∙ᴱ p) ∙ γ

    _＠⊤ : Tm (tyᴹᴿ Γ) → Tm (Γ ⇒ Uᴿ)
    (A ＠⊤) = lam λ γ → (first A ∙ᴱ ⊤) ∙ lamᴿ (λ _ → γ)

    ↓-_ : (A : Tm (tyᴹᴿ Γ))
      → ((i : Tm (El (elᴿ (# p)))) → Tm (El (elᴿ ((A ＠ ⊤) (lamᴿ λ _ → γ ∙ᴿ i)))))
      → Tm (El (elᴿ ((A ＠ p) γ)))
    ↓-_ {p = p} {γ} A f = iso-fwd ((first (second A) ∙ᴱ p) ∙ γ) (lamᴿ f)

    ↑-_ : (A : Tm (tyᴹᴿ Γ))
      → Tm (El (elᴿ ((A ＠ p) γ)))
      → (i : Tm (El (elᴿ (# p))))
      → Tm (El (elᴿ ((A ＠ ⊤) (lamᴿ λ _ → γ ∙ᴿ i))))
    ↑-_ {p = p} {γ} A x i = (iso-bwd ((first (second A) ∙ᴱ p) ∙ γ) x) ∙ᴿ i 

    tmᴹ : (Γ : Conᴹ) → Tm (tyᴹ Γ) → Ty
    tmᴹ Γ A = [ γ ∶ Γ ] ⇒ El (A ∙ γ)

    tmᴹᴿ : (Γ : Conᴹ) → Tm (tyᴹᴿ Γ) → Ty
    tmᴹᴿ Γ A = [ γ ∶ Γ ] ⇒ El (elᴿ ((A ＠⊤) ∙ γ))

    _▷ᴹ_ : (Γ : Conᴹ) → Tm (tyᴹ Γ) → Conᴹ
    Γ ▷ᴹ A = Σᵁ Γ (λ x → A ∙ x)

    idᴹ : Subᴹ Γ Γ
    idᴹ γ = γ

    _∘ᴹ_ : Subᴹ Δ Θ → Subᴹ Γ Δ → Subᴹ Γ Θ
    σ ∘ᴹ τ = λ γ → σ (τ γ)

    _[_]ᴹᵀ : Tm (tyᴹ Γ) → Subᴹ Δ Γ → Tm (tyᴹ Δ)
    A [ σ ]ᴹᵀ = lam (λ δ → A ∙ σ δ)

    _[_]ᴹᵀᴿ : Tm (tyᴹᴿ Γ) → Subᴹ Δ Γ → Tm (tyᴹᴿ Δ)
    A [ σ ]ᴹᵀᴿ = pair
      (lamᴱ λ p → lam λ γ' → (first A ∙ᴱ p) ∙ lamᴿ (λ i → σ (γ' ∙ᴿ i)))
      (pair
        (lamᴱ λ p → lam λ γ' → (first (second A) ∙ᴱ p) ∙ lamᴿ (λ i → σ (γ' ∙ᴿ i)))
        top)

    _[_]ᴹ : (A : Tm (tyᴹ Γ)) (a : Tm (tmᴹ Γ A)) (σ : Subᴹ Δ Γ) → Tm (tmᴹ Δ (A [ σ ]ᴹᵀ))
    _[_]ᴹ A a σ = lam (λ δ → a ∙ σ δ)

    _[_]ᴹᴿ : (A : Tm (tyᴹᴿ Γ)) (a : Tm (tmᴹᴿ Γ A)) (σ : Subᴹ Δ Γ) → Tm (tmᴹᴿ Δ (A [ σ ]ᴹᵀᴿ))
    _[_]ᴹᴿ A a σ = lam (λ δ → a ∙ σ δ)

    pᴹ : (A : Tm (tyᴹ Γ)) → Subᴹ (Γ ▷ᴹ A) Γ
    pᴹ A γ = firstᵁ γ

    qᴹ : (A : Tm (tyᴹ Γ)) → Tm (tmᴹ (Γ ▷ᴹ A) (A [ pᴹ A ]ᴹᵀ))
    qᴹ A = lam (λ γ → secondᵁ γ)

    _,ᴹ_ : {A : Tm (tyᴹ Γ)} (σ : Subᴹ Δ Γ) → Tm (tmᴹ Δ (A [ σ ]ᴹᵀ)) → Subᴹ Δ (Γ ▷ᴹ A)
    (σ ,ᴹ a) δ = pairᵁ (σ δ) (a ∙ δ)

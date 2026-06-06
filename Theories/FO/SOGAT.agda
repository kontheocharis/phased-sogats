module Theories.FO.SOGAT where

open import Utils
open import Theories.FO.CwF
open import Theories.FO.GAT

module InGAT (gat : GAT-ToS) where
  open GAT-ToS gat
  
  variable
    Au Bu A'u B'u : Tm Γ U

  record SOGATCtors : Set₁ where
    field
      Uᴿ : Ty Γ
      Uᴿ[] : Uᴿ {Γ = Δ} [ σ ]T ≡ Uᴿ
      elᴿ : Tm Γ Uᴿ → Tm Γ U
      elᴿ[] : elᴿ a [ σ ] ≡[ ap-Tm U[] ] elᴿ (coe (ap-Tm Uᴿ[]) (a [ σ ]))

      Πᴿ : (a : Tm Γ Uᴿ) → Tm (Γ ▷ El (elᴿ a)) U → Tm Γ U
      lamᴿ : Tm (Γ ▷ El (elᴿ a)) (El Bu) → Tm Γ (El (Πᴿ a Bu))
      appᴿ : Tm Γ (El (Πᴿ a Bu)) → Tm (Γ ▷ El (elᴿ a)) (El Bu)
      Πᴿ-β : appᴿ (lamᴿ a) ≡ a
      Πᴿ-η : lamᴿ (appᴿ a) ≡ a

record SOGAT-ToS : Set₁ where
  field
    gat : GAT-ToS
  open GAT-ToS gat public
  field
    sogat-ctors : InGAT.SOGATCtors gat
  open InGAT.SOGATCtors sogat-ctors public

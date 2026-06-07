module Theories.FO.GAT where

open import Utils
open import Theories.FO.CwF
open import Data.Product using (Σ-syntax)
open import Data.Unit renaming (⊤ to 𝟙)

module InCwF (cwf : CwF) where
  open CwF cwf

  variable
    S : Set
    T : S → Ty Γ
    s : (s : S) → Tm Γ (T s)

  record GATCtors : Set₁ where
    field
      -- Unit
      `1 : Ty Γ
      `1[] : `1 {Γ = Δ} [ σ ]T ≡ `1
      unit-uniq : 𝟙 ≃ Tm Γ `1

      -- Σ
      Σ : (A : Ty Γ) → Ty (Γ ▷ A) → Ty Γ
      Σ[] : (Σ A B) [ σ ]T ≡ Σ (A [ σ ]T) (B [ σ ⁺ ]T)
      pair-proj : (Σ[ a ∈ Tm Γ A ] Tm Γ (B [ < a > ]T)) ≃ Tm Γ (Σ A B)
      -- @@Todo: substitution rules for pair

      -- Universe for sorts
      U : Ty Γ
      U[] : U {Γ = Δ} [ σ ]T ≡ U
      El : Tm Γ U → Ty Γ
      El[] : (El a) [ σ ]T ≡ El (coe (ap-Tm U[]) (a [ σ ]))

      -- Π
      Π : (a : Tm Γ U) → Ty (Γ ▷ El a) → Ty Γ
      Π[] : (Π a B) [ σ ]T ≡ Π (coe (ap-Tm U[]) (a [ σ ]))
        (coe (ap-Ty (cong (_ ▷_) El[])) (B [ σ ⁺ ]T))
      lam-app : Tm (Γ ▷ El a) B ≃ Tm Γ (Π a B)
      lam[] : (lam-app {a = a} {B = B} .to b) [ σ ] ≡[ ap-Tm Π[] ]
        lam-app .to (coe (ap-Tmᶜ (cong (_ ▷_) El[]) refl) (b [ σ ⁺ ]))

      -- Equality
      Eq : Tm Γ A → Tm Γ A → Ty Γ
      Eq[] : (Eq a b) [ σ ]T ≡ Eq (a [ σ ]) (b [ σ ])
      refl-reflect : ((a ≡ b) true) ≃ Tm Γ (Eq a b)
      Refl[] : ∀ {e}
        → (refl-reflect {a = a} {b = b} .to e) [ σ ] ≡[ ap-Tm Eq[] ] refl-reflect .to (by (cong (_[ σ ]) (e .witness)))

      -- External Π
      Πᴱ : (S : Set) → (S → Ty Γ) → Ty Γ
      Πᴱ[] : (Πᴱ S T) [ σ ]T ≡ Πᴱ S (λ x → (T x) [ σ ]T)
      lam-appᴱ : ((s : S) → Tm Γ (T s)) ≃ Tm Γ (Πᴱ S T)
      lamᴱ[] : (lam-appᴱ .to s) [ σ ] ≡[ ap-Tm Πᴱ[] ] lam-appᴱ .to (λ x → s x [ σ ])

record GAT-ToS : Set₂ where
  field
    cwf : CwF
  open CwF cwf public
  field
    gat-ctors : InCwF.GATCtors cwf
  open InCwF.GATCtors gat-ctors public

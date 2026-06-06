module Theories.FO.GAT where

open import Utils
open import Theories.FO.CwF

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
      top : Tm Γ `1
      top[] : top [ σ ] ≡[ ap-Tm `1[] ] top
      `1-η : a ≡ top

      -- Σ
      Σ : (A : Ty Γ) → Ty (Γ ▷ A) → Ty Γ
      Σ[] : (Σ A B) [ σ ]T ≡ Σ (A [ σ ]T) (B [ σ ↑ A ]T)
      pair : (a : Tm Γ A) → Tm Γ (B [ < a > ]T) → Tm Γ (Σ A B)
      fst : Tm Γ (Σ A B) → Tm Γ A
      snd : (s : Tm Γ (Σ A B)) → Tm Γ (B [ < fst s > ]T)
      Σ-β₁ : fst (pair a b) ≡ a
      Σ-β₂ : snd (pair a b) ≡[ ap-Tm (cong (λ x → B [ < x > ]T) Σ-β₁) ] b
      Σ-η : pair (fst a) (snd a) ≡ a

      -- Universe for sorts
      U : Ty Γ
      U[] : U {Γ = Δ} [ σ ]T ≡ U
      El : Tm Γ U → Ty Γ
      El[] : (El a) [ σ ]T ≡ El (coe (ap-Tm U[]) (a [ σ ]))

      -- Π
      Π : (a : Tm Γ U) → Ty (Γ ▷ El a) → Ty Γ
      Π[] : (Π a B) [ σ ]T ≡ Π (coe (ap-Tm U[]) (a [ σ ]))
        (coe (ap-Ty (cong (_ ▷_) El[])) (B [ σ ↑ El a ]T))
      lam : Tm (Γ ▷ El a) B → Tm Γ (Π a B)
      app : Tm Γ (Π a B) → Tm (Γ ▷ El a) B
      Π-β : app (lam a) ≡ a
      Π-η : lam (app a) ≡ a

      -- Equality
      Eq : Tm Γ A → Tm Γ A → Ty Γ
      Eq[] : (Eq a b) [ σ ]T ≡ Eq (a [ σ ]) (b [ σ ])
      Refl : (a ≡ b) true → Tm Γ (Eq a b)
      reflect : Tm Γ (Eq a b) → a ≡ b

      -- External Π
      Πᴱ : (S : Set) → (S → Ty Γ) → Ty Γ
      Πᴱ[] : (Πᴱ S T) [ σ ]T ≡ Πᴱ S (λ x → (T x) [ σ ]T)
      lamᴱ : ((s : S) → Tm Γ (T s)) → Tm Γ (Πᴱ S T)
      appᴱ : Tm Γ (Πᴱ S T) → (s : S) → Tm Γ (T s)
      Πᴱ-β : appᴱ (lamᴱ s) ≡ s
      Πᴱ-η : lamᴱ (appᴱ a) ≡ a

record GAT-ToS : Set₁ where
  field
    cwf : CwF
  open CwF cwf public
  field
    gat-ctors : InCwF.GATCtors cwf
  open InCwF.GATCtors gat-ctors public

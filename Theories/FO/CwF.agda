module Theories.FO.CwF where

open import Utils

record CwFSorts : Set₂ where
  field
    Con : Set₁
    Sub : Con → Con → Set
    Ty : Con → Set
    Tm : (Γ : Con) → Ty Γ → Set

module InCwFSorts (sorts : CwFSorts) where
  open CwFSorts sorts public

  variable
    Γ Δ Θ Γ' Δ' Θ' : Con
    A B A' B' : Ty Γ
    σ τ δ σ' τ' : Sub Γ Δ
    a b a' b' : Tm Γ A

  opaque
    unfolding coe

    ap-Ty : Γ ≡ Δ → Ty Γ ≡ Ty Δ
    ap-Ty refl = refl

    ap-Sub : Γ ≡ Γ' → Δ ≡ Δ' → Sub Γ Δ ≡ Sub Γ' Δ'
    ap-Sub refl refl = refl

    ap-Tm : A ≡ B → Tm Γ A ≡ Tm Γ B
    ap-Tm refl = refl

    ap-Tmᶜ : (eΓ : Γ ≡ Δ) → A ≡[ ap-Ty eΓ ] B → Tm Γ A ≡ Tm Δ B
    ap-Tmᶜ refl refl = refl

  module CwFUtils (_[_]T : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ) where
    opaque
      unfolding coe

      ap-[]T-impl : σ ≡ τ → A [ σ ]T ≡ A [ τ ]T
      ap-[]T-impl refl = refl

      ap-[]T₁-impl : A ≡ B → A [ σ ]T ≡ B [ σ ]T
      ap-[]T₁-impl refl = refl

  record CwFCtors : Set₁ where
    infixl 7 _∘_
    infixl 8 _[_]T
    infixl 8 _[_]
    infixl 5 _▷_
    infixl 5 _,_

    field
      id : Sub Γ Γ
      _∘_ : Sub Δ Θ → Sub Γ Δ → Sub Γ Θ
      id∘ : id ∘ σ ≡ σ
      ∘id : σ ∘ id ≡ σ
      assoc : δ ∘ (σ ∘ τ) ≡ (δ ∘ σ) ∘ τ

      ∙ : Con
      ε : Sub Γ ∙
      ∃!ε : ε ≡ σ

      _[_]T : Ty Δ → Sub Γ Δ → Ty Γ
      [id]T : A [ id ]T ≡ A
      [∘]T : A [ σ ∘ τ ]T ≡ (A [ σ ]T) [ τ ]T

      _[_] : Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
      [id] : a [ id ] ≡[ ap-Tm [id]T ] a
      [∘] : a [ σ ∘ τ ] ≡[ ap-Tm [∘]T ] (a [ σ ]) [ τ ]

      _▷_ : (Γ : Con) → Ty Γ → Con
      p : Sub (Γ ▷ A) Γ
      q : Tm (Γ ▷ A) (A [ p ]T)
      _,_ : (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T) → Sub Γ (Δ ▷ A)
      p∘, : p ∘ (σ , a) ≡ σ
      ,∘ : (σ , a) ∘ τ ≡ ((σ ∘ τ) , coe (ap-Tm (sym ([∘]T {A = A}))) (a [ τ ]))
      p,q : _,_ {A = A} p q ≡ id

    ap-[]T : σ ≡ τ → A [ σ ]T ≡ A [ τ ]T
    ap-[]T = CwFUtils.ap-[]T-impl _[_]T

    ap-[]T₁ : A ≡ B → A [ σ ]T ≡ B [ σ ]T
    ap-[]T₁ = CwFUtils.ap-[]T₁-impl _[_]T

    field
      q[,] : q [ σ , a ] ≡[ ap-Tm (trans (sym [∘]T) (ap-[]T p∘,)) ] a

    _⁺ : (σ : Sub Γ Δ) → Sub (Γ ▷ (A [ σ ]T)) (Δ ▷ A)
    σ ⁺ = ((σ ∘ p) , coe (ap-Tm (sym [∘]T)) q)

    <_> : Tm Γ A → Sub Γ (Γ ▷ A)
    < a > = id , coe (ap-Tm (sym [id]T)) a

    opaque
      unfolding coe
      ap-▷ : (eΓ : Γ ≡ Δ) → A ≡[ ap-Ty eΓ ] B → (Γ ▷ A) ≡ (Δ ▷ B)
      ap-▷ refl refl = refl

record CwF : Set₂ where
  field
    sorts : CwFSorts
  open InCwFSorts sorts public
  field
    ctors : InCwFSorts.CwFCtors sorts
  open InCwFSorts.CwFCtors ctors public

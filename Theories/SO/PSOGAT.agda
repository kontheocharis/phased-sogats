module Theories.SO.PSOGAT where

open import Data.Product using (proj₁; proj₂; _,_; _×_)
open import Utils hiding (⊤; _∧_)
open import Theories.Phase public
open import Theories.SO.GAT
open import Theories.SO.SOGAT

postulate
  In-PSOGAT-ToS : PhaseAlg → Prop
  In-PSOGAT-ToS→In-SOGAT-ToS : ∀ {Φ} → In-PSOGAT-ToS Φ → In-SOGAT-ToS

module PSOGAT-ToS (Φ : PhaseAlg) (s : In-PSOGAT-ToS Φ) where
  open PhaseAlg Φ
  open SOGAT-ToS (In-PSOGAT-ToS→In-SOGAT-ToS s) public

  private variable
    A : Ty
    F : Tm A → Ty
    a b : Tm A
    f : (x : Tm A) → Tm (F x)
    t u : Phase

  postulate
    In : Phase → Set
    In-prop : (x y : In t) → x ≡ y
    in⊤ : In ⊤
    In-and-proj : (In t × In u) ≃ In (t ∧ u)

  In-and : In t → In u → In (t ∧ u)
  In-and x y = In-and-proj .to (x , y)

  In-fst : In (t ∧ u) → In t
  In-fst z = In-and-proj .from z .proj₁

  In-snd : In (t ∧ u) → In u
  In-snd z = In-and-proj .from z .proj₂

  postulate
    Πᴾ : (t : Phase) (F : In t → Ty) → Ty
    ↓ᴾ : ((x : In t) → Tm (F x)) → Tm (Πᴾ t F)
    ↑ᴾ : Tm (Πᴾ t F) → (x : In t) → Tm (F x)
    Πᴾ-β : ↑ᴾ (↓ᴾ f) b ≡ f b
  {-# REWRITE Πᴾ-β #-}
  postulate
    Πᴾ-η : ↓ᴾ (λ x → ↑ᴾ a x) ≡ a
  {-# REWRITE Πᴾ-η #-}

  ↓↑ : ((x : In t) → Tm (F x)) ≃ Tm (Πᴾ t F)
  ↓↑ .to = ↓ᴾ
  ↓↑ .from = ↑ᴾ
  ↓↑ .to-from _ = refl
  ↓↑ .from-to _ = refl

  postulate
    Πᴾᵁ : (t : Phase) (f : In t → Tm U) → Tm U
    ↓ᴾᵁ : ((x : In t) → Tm (El (f x))) → Tm (El (Πᴾᵁ t f))
    ↑ᴾᵁ : Tm (El (Πᴾᵁ t f)) → (x : In t) → Tm (El (f x))
    Πᴾᵁ-β : ↑ᴾᵁ (↓ᴾᵁ f) b ≡ f b
  {-# REWRITE Πᴾᵁ-β #-}
  postulate
    Πᴾᵁ-η : ↓ᴾᵁ (λ x → ↑ᴾᵁ a x) ≡ a
  {-# REWRITE Πᴾᵁ-η #-}

  ↓↑ᵁ : ((x : In t) → Tm (El (f x))) ≃ Tm (El (Πᴾᵁ t f))
  ↓↑ᵁ .to = ↓ᴾᵁ
  ↓↑ᵁ .from = ↑ᴾᵁ
  ↓↑ᵁ .to-from _ = refl
  ↓↑ᵁ .from-to _ = refl

  postulate
    Πᴾᴿ : (t : Phase) (f : In t → Tm Uᴿ) → Tm Uᴿ
    ↓ᴾᴿ : ((x : In t) → Tm (El (elᴿ (f x)))) → Tm (El (elᴿ (Πᴾᴿ t f)))
    ↑ᴾᴿ : Tm (El (elᴿ (Πᴾᴿ t f))) → (x : In t) → Tm (El (elᴿ (f x)))
    Πᴾᴿ-β : ↑ᴾᴿ (↓ᴾᴿ f) b ≡ f b
  {-# REWRITE Πᴾᴿ-β #-}
  postulate
    Πᴾᴿ-η : ↓ᴾᴿ (λ x → ↑ᴾᴿ a x) ≡ a
  {-# REWRITE Πᴾᴿ-η #-}

  ↓↑ᴿ : ((x : In t) → Tm (El (elᴿ (f x)))) ≃ Tm (El (elᴿ (Πᴾᴿ t f)))
  ↓↑ᴿ .to = ↓ᴾᴿ
  ↓↑ᴿ .from = ↑ᴾᴿ
  ↓↑ᴿ .to-from _ = refl
  ↓↑ᴿ .from-to _ = refl

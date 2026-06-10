module Theories.SO.SOGAT where

open import Utils hiding (⊤; _∧_)
open import Theories.SO.GAT

postulate
  In-SOGAT-ToS : Prop
  In-SOGAT-ToS→In-GAT-ToS : In-SOGAT-ToS → In-GAT-ToS

module SOGAT-ToS (s : In-SOGAT-ToS) where
  open GAT-ToS (In-SOGAT-ToS→In-GAT-ToS s) public

  private variable
    A : Ty
    F : Tm A → Ty
    a b : Tm A
    f : (x : Tm A) → Tm (F x)

  postulate
    Uᴿ : Ty
    elᴿ : Tm Uᴿ → Tm U
    Πᴿ : (a : Tm Uᴿ) → (Tm (El (elᴿ a)) → Tm U) → Tm U
    lamᴿ : ((x : Tm (El (elᴿ a))) → Tm (El (f x))) → Tm (El (Πᴿ a f))
    _∙ᴿ_ : Tm (El (Πᴿ a f)) → (x : Tm (El (elᴿ a))) → Tm (El (f x))
    Πᴿ-β : (lamᴿ f) ∙ᴿ b ≡ f b
  {-# REWRITE Πᴿ-β #-}
  postulate
    Πᴿ-η : lamᴿ (a ∙ᴿ_) ≡ a
  {-# REWRITE Πᴿ-η #-}

  syntax Πᴿ a (λ x → B) = [ x ∶ a ] ⇒ᴿ B

  infixr 3 _⇒ᴿ_
  _⇒ᴿ_ : Tm Uᴿ → Tm U → Tm U
  A ⇒ᴿ B = Πᴿ A (λ _ → B)

  lam-appᴿ : ((x : Tm (El (elᴿ a))) → Tm (El (f x))) ≃ Tm (El (Πᴿ a f))
  lam-appᴿ .to = lamᴿ
  lam-appᴿ .from = _∙ᴿ_
  lam-appᴿ .to-from _ = refl
  lam-appᴿ .from-to _ = refl

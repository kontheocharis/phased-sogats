module Theories.SO.SOGAT where

open import Utils hiding (⊤; _∧_)
open import Theories.SO.GAT

module in-GAT (gat : GAT-ToS) where
  open GAT-ToS gat

  variable
    A : Ty
    F : Tm A → Ty
    a : Tm A
    f : (x : Tm A) → Tm (F x)

  record SOGAT-ToSᶜ : Set₁ where
    field
      Uᴿ : Ty
      elᴿ : Tm Uᴿ → Tm U

      Πᴿ : (a : Tm Uᴿ) → (Tm (El (elᴿ a)) → Tm U) → Tm U
      lam-appᴿ : ((a : Tm (El (elᴿ a))) → Tm (El (f a))) ≃ Tm (El (Πᴿ a f))

    syntax Πᴿ a (λ x → B) = [ x ∶ a ] ⇒ᴿ B

    infixr 3 _⇒ᴿ_
    _⇒ᴿ_ : Tm Uᴿ → Tm U → Tm U
    A ⇒ᴿ B = Πᴿ A (λ _ → B)

    _∙ᴿ_ : Tm (El (Πᴿ a f)) → (x : Tm (El (elᴿ a))) → Tm (El (f x))
    _∙ᴿ_ = lam-appᴿ .from

    lamᴿ : ((x : Tm (El (elᴿ a))) → Tm (El (f x))) → Tm (El (Πᴿ a f))
    lamᴿ = lam-appᴿ .to

record SOGAT-ToS : Set₁ where
  field
    gat : GAT-ToS
  open GAT-ToS gat public
  field
    sogat-ctors : in-GAT.SOGAT-ToSᶜ gat
  open in-GAT.SOGAT-ToSᶜ sogat-ctors public

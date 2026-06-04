module Main where

open import Data.Product using (Σ-syntax; proj₁; proj₂; _,_)
open import Data.Unit using () renaming (⊤ to 𝟙)
open import Utils hiding (⊤; _∧_)

record GAT-ToSˢ : Set₁ where
  field
    Ty : Set
    Tm : Ty → Set

variable
  S : Set
  t u v : S

record PhaseAlg : Set₁ where
  field
    Phase : Set
    _∧_ : Phase → Phase → Phase
    ⊤ : Phase
    ∧assoc : (t ∧ u) ∧ v ≡ t ∧ (u ∧ v)
    ∧comm : t ∧ u ≡ u ∧ t
    ∧idemp : t ∧ t ≡ t
    ∧⊤ : t ∧ ⊤ ≡ t

module in-GAT-ToSˢ (s : GAT-ToSˢ) where
  open GAT-ToSˢ s

  variable
    A B C : Ty
    F G H : Tm A → Ty
    a b c : Tm A
    f g h : (x : Tm A) → Tm (F x)

    P : Prop
    m n : P → Tm _
    X : S → Ty
    

  record GAT-ToSᶜ : Set₁ where
    field
      Σ : (A : Ty) → (Tm A → Ty) → Ty
      pair-proj : Σ[ a ∈ Tm A ] Tm (F a) ≃ Tm (Σ A F)

      `1 : Ty
      unit-uniq : 𝟙 ≃ Tm `1

      U : Ty
      El : Tm U → Ty

      Π : (a : Tm U) → (Tm (El a) → Ty) → Ty
      lam-app : ((a : Tm (El a)) → Tm (F a)) ≃ Tm (Π a F)
  
      Eq : Tm A → Tm A → Ty
      refl-reflect : ((a ≡ b) true) ≃ Tm (Eq a b)

      Πᴱ : (S : Set) → (S → Ty) → Ty
      lam-appᴱ : ((s : S) → Tm (X s)) ≃ Tm (Πᴱ S X)


    syntax Σ A (λ x → B) = x ∶ A ⨾ B
    syntax Π A (λ x → B) = [ x ∶ A ] ⇒ B

    infixr 3 _⇒_
    _⇒_ : Tm U → Ty → Ty
    A ⇒ B = Π A (λ _ → B)


  record SOGAT-ToSᶜ : Set₁ where
    field
      gat : GAT-ToSᶜ
    open GAT-ToSᶜ gat
    field
      Uᴿ : Ty
      elᴿ : Tm Uᴿ → Tm U

      Πᴿ : (a : Tm Uᴿ) → (Tm (El (elᴿ a)) → Tm U) → Tm U
      lam-appᴿ : ((a : Tm (El (elᴿ a))) → Tm (El (f a))) ≃ Tm (El (Πᴿ a f))

    syntax Πᴿ a (λ x → B) = [ x ∶ a ] ⇒ᴿ B

    infixr 3 _⇒ᴿ_
    _⇒ᴿ_ : Tm Uᴿ → Tm U → Tm U
    A ⇒ᴿ B = Πᴿ A (λ _ → B)
      
      
  record PSOGAT-ToSᶜ (Φ : PhaseAlg) : Set₁ where
    open PhaseAlg Φ
    field
      sogat : SOGAT-ToSᶜ
    open SOGAT-ToSᶜ sogat
    open GAT-ToSᶜ gat
    field

      In : Phase → Prop
      Πᴾ : (p : Phase) → (In p → Tm Uᴿ) → Tm Uᴿ
      ↓↑ : ((a : In t) → Tm (El (elᴿ (m a)))) ≃ Tm (El (elᴿ (Πᴾ t m)))


record GAT-ToS : Set₁ where
  field
    gat-sorts : GAT-ToSˢ
  open GAT-ToSˢ gat-sorts public
  open in-GAT-ToSˢ gat-sorts public
  field
    gat-ctors : GAT-ToSᶜ
  open GAT-ToSᶜ gat-ctors public

record SOGAT-ToS : Set₁ where
  field
    gat : GAT-ToS
  open GAT-ToS gat public
  field
    sogat-ctors : SOGAT-ToSᶜ
  open SOGAT-ToSᶜ sogat-ctors public

record PSOGAT-ToS (Φ : PhaseAlg) : Set₁ where
  field
    sogat : SOGAT-ToS
  open SOGAT-ToS sogat public
  field
    psogat-ctors : PSOGAT-ToSᶜ Φ
  open PSOGAT-ToSᶜ psogat-ctors public


-- module PSOGAT⇒SOGAT
--   (sogat : SOGAT-ToSᶜ)
--   where

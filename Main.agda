module Main where

open import Data.Product using (Σ-syntax; proj₁; proj₂; _,_)
open import Data.Unit using () renaming (⊤ to 𝟙)
open import Utils

record GAT-ToSˢ : Set₁ where
  field
    Ty : Set
    Tm : Ty → Set

module in-GAT-ToSˢ (s : GAT-ToSˢ) where
  open GAT-ToSˢ s

  variable
    A B C : Ty
    F G H : Tm A → Ty
    a b c : Tm A
    f g h : (x : Tm A) → Tm (F x)

    S : Set
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


  record SOGAT-ToSᶜ : Set₁ where
    field
      gat : GAT-ToSᶜ
    open GAT-ToSᶜ gat
    field
      Uᴿ : Ty
      elᴿ : Tm Uᴿ → Tm U

      Πᴿ : (a : Tm Uᴿ) → (Tm (El (elᴿ a)) → Tm U) → Tm U
      lam-appᴿ : ((a : Tm (El (elᴿ a))) → Tm (El (f a))) ≃ Tm (El (Πᴿ a f))
      
      

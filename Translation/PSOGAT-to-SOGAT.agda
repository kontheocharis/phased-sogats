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

  -- Strictify phase laws
  opaque
    Phase : Set
    Phase = Φ .PhaseAlg.Phase

    _∧_ : Phase → Phase → Phase
    _∧_ = Φ .PhaseAlg._∧_

    ⊤ : Phase
    ⊤ = Φ .PhaseAlg.⊤

    variable
      p q t u v : Phase

    ∧assoc : (t ∧ u) ∧ v ≡ t ∧ (u ∧ v)
    ∧assoc = Φ .PhaseAlg.∧assoc

    ∧comm : t ∧ u ≡ u ∧ t
    ∧comm = Φ .PhaseAlg.∧comm

    ∧idemp : t ∧ t ≡ t
    ∧idemp = Φ .PhaseAlg.∧idemp

    ∧⊤ : t ∧ ⊤ ≡ t
    ∧⊤ = Φ .PhaseAlg.∧⊤

    ⊤∧ : ⊤ ∧ t ≡ t
    ⊤∧ = trans ∧comm ∧⊤

  {-# REWRITE ∧idemp ∧⊤ ⊤∧ #-}

  module _
    (# : Phase → Tm Uᴿ)
    (#-prop : ∀ {p} (i j : Tm (El (elᴿ (# p)))) → i ≡ j)
    (#⊤ : Tm (El (elᴿ (# ⊤))))
    (#∧ : ∀ {p q} → Tm (Iso (Σᵁ (elᴿ (# p)) (λ _ → elᴿ (# q))) (elᴿ (# (p ∧ q)))))
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

    -- First, we build a (Πᴿ, In(Φ))-CwF M where the types are Ty valued.
    -- Then, Psh(M) will support a model of PSOGAT-ToS(Φ).

    -- Category
    Conᴹ : Set
    Conᴹ = Tm U

    variable
      Γ Δ Θ : Conᴹ

    Subᴹ : (Γ Δ : Conᴹ) → Set
    Subᴹ Γ Δ = Tm (El Γ) → Tm (El Δ)

    idᴹ : Subᴹ Γ Γ
    idᴹ γ = γ

    _∘ᴹ_ : Subᴹ Δ Θ → Subᴹ Γ Δ → Subᴹ Γ Θ
    σ ∘ᴹ τ = λ γ → σ (τ γ)
    -- @@Todo: laws

    -- Terminal object
    ∙ᴹ : Conᴹ
    ∙ᴹ = 1ᵁ

    εᴹ : Subᴹ Γ ∙ᴹ
    εᴹ _ = topᵁ

    ε-uniqᴹ : (σ : Subᴹ Γ ∙ᴹ) → σ ≡ εᴹ
    ε-uniqᴹ σ = funext λ γ → top-uniqᵁ (σ γ)

    variable
      σ : Subᴹ Γ Δ

    -- Presheaves
    tyᴹ : (Γ : Conᴹ) → Ty
    tyᴹ Γ = Γ ⇒ U

    -- Here is the main trick.
    -- Representable types carry a code for each phase, and an iso that says
    -- actually each is isomorphic to the top code under that phase.
    --
    -- We only need to do this because SOGATs only allow second-order
    -- quantification; We are not allowed to write
    --    ((# p -> X ⊤) -> Y) -> Z.
    -- but we can write
    --    (X p -> Y) -> Z.
    -- and this is equivalent by the iso below.
    tyᴹᴿ : (Γ : Conᴹ) → Ty
    tyᴹᴿ Γ =
      X ∶ [ p ∶ Phase ] ⇒ᴱ [ γ ∶ # p ⇒ᴿ Γ ] ⇒ Uᴿ ⨾
      ↓↑ ∶ [ p ∶ Phase ] ⇒ᴱ ([ γ ∶ # p ⇒ᴿ Γ ]
        ⇒ Iso
          ([ i ∶ # p ] ⇒ᴿ elᴿ ((X ∙ᴱ ⊤) ∙ lamᴿ λ _ → γ ∙ᴿ i))
          (elᴿ ((X ∙ᴱ p) ∙ γ))) ⨾
      `1 -- @@Todo: add a law that the top iso is identity

    variable
      A B : Tm (tyᴹ Γ)
      Aᴿ Bᴿ : Tm (tyᴹᴿ Γ)
      γ : Tm (El Γ)

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

    ιᴹᴿ : Tm (tyᴹᴿ Γ) → Tm (tyᴹ Γ)
    ιᴹᴿ A = lam λ γ → elᴿ ((A ＠⊤) ∙ γ)

    tmᴹ : (Γ : Conᴹ) → Tm (tyᴹ Γ) → Ty
    tmᴹ Γ A = [ γ ∶ Γ ] ⇒ El (A ∙ γ)

    tmᴹᴿ : (Γ : Conᴹ) → Tm (tyᴹᴿ Γ) → Ty
    tmᴹᴿ Γ A = [ γ ∶ Γ ] ⇒ El (elᴿ ((A ＠⊤) ∙ γ))

    _[_]ᴹᵀ : Tm (tyᴹ Γ) → Subᴹ Δ Γ → Tm (tyᴹ Δ)
    A [ σ ]ᴹᵀ = lam (λ δ → A ∙ σ δ)

    _[_]ᴹᵀᴿ : Tm (tyᴹᴿ Γ) → Subᴹ Δ Γ → Tm (tyᴹᴿ Δ)
    A [ σ ]ᴹᵀᴿ = pair
      (lamᴱ λ p → lam λ γ' → (first A ∙ᴱ p) ∙ lamᴿ (λ i → σ (γ' ∙ᴿ i)))
      (pair
        (lamᴱ λ p → lam λ γ' → (first (second A) ∙ᴱ p) ∙ lamᴿ (λ i → σ (γ' ∙ᴿ i)))
        top)

    _[_]ᴹ : (a : Tm (tmᴹ Γ A)) (σ : Subᴹ Δ Γ) → Tm (tmᴹ Δ (A [ σ ]ᴹᵀ))
    _[_]ᴹ a σ = lam (λ δ → a ∙ σ δ)

    _[_]ᴹᴿ : (a : Tm (tmᴹᴿ Γ Aᴿ)) (σ : Subᴹ Δ Γ) → Tm (tmᴹᴿ Δ (Aᴿ [ σ ]ᴹᵀᴿ))
    _[_]ᴹᴿ a σ = lam (λ δ → a ∙ σ δ)

    -- @@Todo: equations

    -- Context extensions
    opaque
      _▷ᴹ_ : (Γ : Conᴹ) → Tm (tyᴹ Γ) → Conᴹ
      Γ ▷ᴹ A = Σᵁ Γ (λ x → A ∙ x)

    opaque
      unfolding _▷ᴹ_

      pᴹ : Subᴹ (Γ ▷ᴹ A) Γ
      pᴹ γ = firstᵁ γ

      qᴹ : Tm (tmᴹ (Γ ▷ᴹ A) (A [ pᴹ {A = A} ]ᴹᵀ))
      qᴹ = lam (λ γ → secondᵁ γ)

      _,ᴹ_ : (σ : Subᴹ Γ Δ) → Tm (tmᴹ Γ (A [ σ ]ᴹᵀ)) → Subᴹ Γ (Δ ▷ᴹ A)
      (σ ,ᴹ a) δ = pairᵁ (σ δ) (a ∙ δ)

      -- @@Todo: equations

    opaque
      _▷ᴵᴹ_ : Conᴹ → Phase → Conᴹ
      Γ ▷ᴵᴹ t = Σᵁ Γ (λ _ → elᴿ (# t))

    opaque
      unfolding _▷ᴵᴹ_

      inᴹ : Conᴹ → Phase → Ty
      inᴹ Γ t = Γ ⇒ El (elᴿ (# t))

      pᴵᴹ : Subᴹ (Γ ▷ᴵᴹ t) Γ
      pᴵᴹ γ = firstᵁ γ

      qᴵᴹ : Tm (inᴹ (Γ ▷ᴵᴹ t) t)
      qᴵᴹ = lam λ γ → secondᵁ γ

      _,ᴵᴹ_ : Subᴹ Δ Γ → Tm (inᴹ Δ t) → Subᴹ Δ (Γ ▷ᴵᴹ t)
      (σ ,ᴵᴹ i) δ = pairᵁ (σ δ) (i ∙ δ)

    -- Type formers
    opaque
      unfolding _,ᴹ_ _,ᴵᴹ_

      Unitᴹ : Tm (tyᴹ Γ)
      Unitᴹ = lam λ _ → 1ᵁ

      unitᴹ : Tm (tmᴹ Γ Unitᴹ)
      unitᴹ = lam λ _ → topᵁ

      unit-uniqᴹ : (a : Tm (tmᴹ Γ Unitᴹ)) → a ≡ unitᴹ
      unit-uniqᴹ a = cong lam (funext λ γ → top-uniqᵁ (a ∙ γ))

      Σᴹ : (A : Tm (tyᴹ Γ)) → Tm (tyᴹ (Γ ▷ᴹ A)) → Tm (tyᴹ Γ)
      Σᴹ A B = lam λ γ → Σᵁ (A ∙ γ) (λ x → B ∙ pairᵁ γ x)

      ⟨_⟩ᴹ : Tm (tmᴹ Γ A) → Subᴹ Γ (Γ ▷ᴹ A)
      ⟨_⟩ᴹ {A = A} a = _,ᴹ_ {A = A} idᴹ a

      pair-projᴹ : (Σ[ a ∈ Tm (tmᴹ Γ A) ] Tm (tmᴹ Γ (B [ ⟨ a ⟩ᴹ ]ᴹᵀ))) ≃ Tm (tmᴹ Γ (Σᴹ A B))
      pair-projᴹ .to (a ,, b) = lam λ γ → pairᵁ (a ∙ γ) (b ∙ γ)
      pair-projᴹ .from p = (lam λ γ → firstᵁ (p ∙ γ)) ,, (lam λ γ → secondᵁ (p ∙ γ))
      pair-projᴹ .to-from _ = refl
      pair-projᴹ .from-to _ = refl

      elᴿᴹ : Tm (tyᴹᴿ Γ) → Tm (tyᴹ Γ)
      elᴿᴹ A = lam (λ γ → elᴿ ((A ＠⊤) ∙ γ))

      Πᴿᴹ : (a : Tm (tyᴹᴿ Γ)) → Tm (tyᴹ (Γ ▷ᴹ elᴿᴹ a)) → Tm (tyᴹ Γ)
      Πᴿᴹ a B = lam (λ γ → Πᴿ ((a ＠⊤) ∙ γ) (λ x → B ∙ pairᵁ γ x))

      lam-appᴿᴹ : Tm (tmᴹ (Γ ▷ᴹ elᴿᴹ Aᴿ) B) ≃ Tm (tmᴹ Γ (Πᴿᴹ Aᴿ B))
      lam-appᴿᴹ .to f = lam λ γ → lamᴿ λ x → f ∙ pairᵁ γ x
      lam-appᴿᴹ .from g = lam λ γ → (g ∙ firstᵁ γ) ∙ᴿ secondᵁ γ
      lam-appᴿᴹ .to-from _ = refl
      lam-appᴿᴹ .from-to _ = refl

      Πᴾᴹ : (t : Phase) → Tm (tyᴹ (Γ ▷ᴵᴹ t)) → Tm (tyᴹ Γ)
      Πᴾᴹ t B = lam (λ γ → Πᴿ (# t) (λ i → B ∙ pairᵁ γ i))

      #-π₁ : Tm (El (elᴿ (# (p ∧ q)))) → Tm (El (elᴿ (# p)))
      #-π₁ {p} {q} j = firstᵁ (iso-bwd (#∧ {p} {q}) j)

      #-π₂ : Tm (El (elᴿ (# (p ∧ q)))) → Tm (El (elᴿ (# q)))
      #-π₂ {p} {q} j = secondᵁ (iso-bwd (#∧ {p} {q}) j)

      #-pair : Tm (El (elᴿ (# p))) → Tm (El (elᴿ (# q))) → Tm (El (elᴿ (# (p ∧ q))))
      #-pair i k = iso-fwd #∧ (pairᵁ i k)

      Πᴾᴿᴹ : (t : Phase) → Tm (tyᴹᴿ (Γ ▷ᴵᴹ t)) → Tm (tyᴹᴿ Γ)
      Πᴾᴿᴹ t B = pair
        (lamᴱ λ p → lam λ γ →
          (first B ∙ᴱ (p ∧ t)) ∙ lamᴿ (λ j → pairᵁ (γ ∙ᴿ #-π₁ j) (#-π₂ j)))
        (pair (lamᴱ λ p → lam λ γ →
          iso (λ input →
            iso-fwd
              ((first (second B) ∙ᴱ (p ∧ t)) ∙
                lamᴿ (λ j → pairᵁ (γ ∙ᴿ #-π₁ j) (#-π₂ j)))
              (lamᴿ (λ j →
                coe (cong (λ y → Tm (El (elᴿ ((first B ∙ᴱ ⊤) ∙
                  lamᴿ (λ _ → pairᵁ (γ ∙ᴿ #-π₁ {p} {t} j) y)))))
                    (#-prop (#-π₂ (#-π₂ {p} {t} j)) (#-π₂ j)))
                  ((iso-bwd ((first (second B) ∙ᴱ t) ∙
                    lamᴿ (λ k → pairᵁ (γ ∙ᴿ #-π₁ j) (#-π₂ k)))
                      (input ∙ᴿ #-π₁ j))
                  ∙ᴿ #-π₂ j))))
          (λ output →
            lamᴿ (λ i →
              iso-fwd
                ((first (second B) ∙ᴱ t) ∙
                  lamᴿ (λ k → pairᵁ (γ ∙ᴿ i) (#-π₂ k)))
                (lamᴿ (λ k →
                  coe (cong (λ pr → Tm (El (elᴿ ((first B ∙ᴱ ⊤) ∙ lamᴿ (λ _ → pr)))))
                    (cong₂ pairᵁ (cong (γ ∙ᴿ_) (#-prop (#-π₁ (#-pair i k)) i))
                      (#-prop (#-π₂ (#-pair i k)) (#-π₂ k))))
                    ((iso-bwd ((first (second B) ∙ᴱ (p ∧ t)) ∙
                      lamᴿ (λ j → pairᵁ (γ ∙ᴿ #-π₁ j) (#-π₂ {p} {t} j)))
                    output)
                  ∙ᴿ #-pair i k)))))
            {!!}  -- oh god
            {!!})
          top)

      ↑↓ᵁᴹ : Tm (tmᴹ (Γ ▷ᴵᴹ t) A) ≃ Tm (tmᴹ Γ (Πᴾᴹ t A))
      ↑↓ᵁᴹ .to f = lam λ γ → lamᴿ λ j → f ∙ pairᵁ γ j
      ↑↓ᵁᴹ .from g = lam λ γ → (g ∙ firstᵁ γ) ∙ᴿ secondᵁ γ
      ↑↓ᵁᴹ .to-from _ = refl
      ↑↓ᵁᴹ .from-to _ = refl

      ↑↓ᴿᴹ : Tm (tmᴹᴿ (Γ ▷ᴵᴹ t) Aᴿ) ≃ Tm (tmᴹᴿ Γ (Πᴾᴿᴹ t Aᴿ))
      ↑↓ᴿᴹ {t = t} {Aᴿ = Aᴿ} .to f = lam λ γ →
        ↓-_ {p = t} {γ = lamᴿ λ j → pairᵁ γ (#-π₂ {⊤} {t} j)} Aᴿ
          λ i → f ∙ pairᵁ γ (#-π₂ {⊤} {t} i)
      ↑↓ᴿᴹ {t = t} {Aᴿ = Aᴿ} .from g = lam λ γ →
        coe (cong (λ y → Tm (El (elᴿ ((Aᴿ ＠ ⊤) (lamᴿ λ _ → pairᵁ (firstᵁ γ) y)))))
                  (#-prop (#-π₂ {⊤} {t} (secondᵁ γ)) (secondᵁ γ)))
          (↑-_ {p = t} {γ = lamᴿ λ j → pairᵁ (firstᵁ γ) (#-π₂ {⊤} {t} j)} Aᴿ
            (g ∙ firstᵁ γ) (secondᵁ γ))
      ↑↓ᴿᴹ .to-from _ = {!!}
      ↑↓ᴿᴹ .from-to _ = {!!}

module Translation where

open import Data.Product using (proj₁; proj₂; _,_; _×_)
open import Utils hiding (⊤; _∧_)
open import ToS

module PSOGAT⇒SOGAT (sg : SOGAT-ToS) (Φ : PhaseAlg) where
  module G = GAT-ToS
  module Gˢ = GAT-ToSˢ
  module Gᶜ = in-GAT-ToSˢ.GAT-ToSᶜ

  module SG = SOGAT-ToS
  module SGᶜ = in-GAT-ToSˢ.SOGAT-ToSᶜ

  module PSG = PSOGAT-ToS
  module PSGᶜ = in-GAT-ToSˢ.PSOGAT-ToSᶜ

  open SOGAT-ToS sg
  open PhaseAlg Φ

  module _
    (In : Phase → Tm Uᴿ)
    (in⊤ : Tm (El (elᴿ (In ⊤))))
    (In-prop : ∀ {t} (x y : Tm (El (elᴿ (In t)))) → x ≡ y)
    (In-and-proj : ∀ {t u} → (Tm (El (elᴿ (In t))) × Tm (El (elᴿ (In u)))) ≃ Tm (El (elᴿ (In (t ∧ u)))))
    where

    In-and : Tm (El (elᴿ (In t))) → Tm (El (elᴿ (In u)))
           → Tm (El (elᴿ (In (t ∧ u))))
    In-and x y = In-and-proj .to (x , y)

    In-fst : Tm (El (elᴿ (In (t ∧ u)))) → Tm (El (elᴿ (In t)))
    In-fst z = In-and-proj .from z .proj₁

    In-snd : Tm (El (elᴿ (In (t ∧ u)))) → Tm (El (elᴿ (In u)))
    In-snd z = In-and-proj .from z .proj₂

    ps : PSOGAT-ToS Φ
    ps .PSG.sogat .SG.gat .G.gat-sorts .Gˢ.Ty = Ty
    ps .PSG.sogat .SG.gat .G.gat-sorts .Gˢ.Tm = Tm
    ps .PSG.sogat .SG.gat .G.gat-ctors .Gᶜ.Σ = Σ
    ps .PSG.sogat .SG.gat .G.gat-ctors .Gᶜ.pair-proj = pair-proj
    ps .PSG.sogat .SG.gat .G.gat-ctors .Gᶜ.`1 = `1
    ps .PSG.sogat .SG.gat .G.gat-ctors .Gᶜ.unit-uniq = unit-uniq

    ps .PSG.sogat .SG.gat .G.gat-ctors .Gᶜ.U
      = X ∶ [ p ∶ Phase ] ⇒ᴱ U ⨾
        ↓↑ ∶ [ p ∶ Phase ] ⇒ᴱ (Iso (In p ⇒ᴿ X ∙ᴱ ⊤) (X ∙ᴱ p)) ⨾
        `1

    ps .PSG.sogat .SG.gat .G.gat-ctors .Gᶜ.El X = El (first X ∙ᴱ ⊤)
    ps .PSG.sogat .SG.gat .G.gat-ctors .Gᶜ.Π A F = Π (first A ∙ᴱ ⊤) F
    ps .PSG.sogat .SG.gat .G.gat-ctors .Gᶜ.lam-app = lam-app
    ps .PSG.sogat .SG.gat .G.gat-ctors .Gᶜ.Eq = Eq
    ps .PSG.sogat .SG.gat .G.gat-ctors .Gᶜ.refl-reflect = refl-reflect
    ps .PSG.sogat .SG.gat .G.gat-ctors .Gᶜ.Πᴱ = Πᴱ
    ps .PSG.sogat .SG.gat .G.gat-ctors .Gᶜ.lam-appᴱ = lam-appᴱ

    ps .PSG.sogat .SG.sogat-ctors .SGᶜ.Uᴿ
      = X ∶ [ p ∶ Phase ] ⇒ᴱ Uᴿ ⨾
        ↓↑ ∶ [ p ∶ Phase ] ⇒ᴱ (Iso (In p ⇒ᴿ elᴿ (X ∙ᴱ ⊤)) (elᴿ (X ∙ᴱ p))) ⨾
        `1

    ps .PSG.sogat .SG.sogat-ctors .SGᶜ.elᴿ X
      = pair (lamᴱ λ p → elᴿ (first X ∙ᴱ p))
        (coe
          (cong Tm (cong (λ s → Σ (Πᴱ Phase s) (λ _ → `1))
          (funext (λ p → cong₂ Iso (cong (In p ⇒ᴿ_) (sym lamᴱ-appᴱ )) (sym lamᴱ-appᴱ)))))
        (second X))
    ps .PSG.sogat .SG.sogat-ctors .SGᶜ.Πᴿ a F
      = pair (lamᴱ λ p → Πᴿ (first a ∙ᴱ ⊤) (λ x⊤ → first (F ({!!})) ∙ᴱ p)) ({!!})
    ps .PSG.sogat .SG.sogat-ctors .SGᶜ.lam-appᴿ {a = a} {f = f} = {!!}
    ps .PSG.psogat-ctors .PSGᶜ.In p = Tm (El (elᴿ (In p)))
    ps .PSG.psogat-ctors .PSGᶜ.In-prop = In-prop
    ps .PSG.psogat-ctors .PSGᶜ.in⊤ = in⊤
    ps .PSG.psogat-ctors .PSGᶜ.In-and-proj = In-and-proj
    ps .PSG.psogat-ctors .PSGᶜ.Πᴾ p X
      = pair (lamᴱ λ p' → first X ∙ᴱ (p ∧ p'))
        (pair (lamᴱ λ p' →
          iso {!  !} {!  !} (λ x → {!!}) (λ x → {!!}))
          top)
    ps .PSG.psogat-ctors .PSGᶜ.↓↑ {t = t} {a = a} = {!!}
    ps .PSG.psogat-ctors .PSGᶜ.Πᴾᴿ p X
      = pair (lamᴱ λ p' → first X ∙ᴱ (p ∧ p'))
        (pair (lamᴱ λ p' →
          iso {! !} {!  !} (λ x → {!!}) (λ x → {!!}))
          top)
    ps .PSG.psogat-ctors .PSGᶜ.↓↑ᴿ {t = t} {a = a} = {!!}

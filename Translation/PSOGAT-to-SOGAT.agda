module Translation.PSOGAT-to-SOGAT where

open import Theories.Phase
import Theories.SO.SOGAT as SO
import Theories.FO.CwF as FO-CwF
import Theories.FO.GAT as FO-GAT
import Theories.FO.SOGAT as FO-SOGAT
import Theories.FO.PSOGAT as FO
open import Utils hiding (⊤; _∧_)

module PSOGAT-to-SOGAT (Φ : PhaseAlg) (sogat : SO.SOGAT-ToS) where
  -- In here, we pretend to be in a two-level type theory where the
  -- object theory is the SOGAT ToS, given by the `sogat` module parameter.
  open SO.SOGAT-ToS sogat
  open InPhaseAlg Φ

  -- What we will do is build a model of PSOGAT ToS in Psh(Φ, Ty), that is,
  -- presheaves over the input phase algebra, valued in the object universe.

  module P = FO.PSOGAT-ToS
  module S = FO-SOGAT.SOGAT-ToS
  module G = FO-GAT.GAT-ToS
  module C = FO-CwF.CwF
  module Cˢ = FO-CwF.CwFSorts
  module Cᶜ = FO-CwF.InCwFSorts.CwFCtors
  module Gᶜ = FO-GAT.InCwF.GATCtors
  module Sᶜ = FO-SOGAT.InGAT.SOGATCtors
  module Pᶜ = FO.InSOGAT.PSOGATCtors

  variable
    le : q ≤ p
    le' : r ≤ q

  record Conᴹ : Set where
    field
      obj  : Phase → Ty
      rest : q ≤ p → Tm (obj p) → Tm (obj q)
      rest-id : {γ : Tm (obj p)} → rest ≤-refl γ ≡ γ
      rest-⊙ : {γ : Tm (obj p)} → rest (le' ⊙ le) γ ≡ rest le' (rest le γ)

  variable
    Γ Δ Θ : Conᴹ

  record Subᴹ (Δ Γ : Conᴹ) : Set where
    field
      map : Tm (Conᴹ.obj Δ p) → Tm (Conᴹ.obj Γ p)
      nat : ∀ {δ} → Conᴹ.rest Γ le (map δ) ≡ map (Conᴹ.rest Δ le δ)

  record Tyᴹ (Γ : Conᴹ) : Set where
    field
      fib  : Tm (Conᴹ.obj Γ p) → Ty
      rest : (le : q ≤ p) (γ : Tm (Conᴹ.obj Γ p))
        → Tm (fib γ) → Tm (fib (Conᴹ.rest Γ le γ))
      rest-id : ∀ {γ : Tm (Conᴹ.obj Γ p)} {a}
        → rest ≤-refl γ a ≡[ cong Tm (cong fib (Conᴹ.rest-id Γ {γ = γ})) ] a
      rest-⊙ : ∀ {γ : Tm (Conᴹ.obj Γ p)} {a}
        → rest (le' ⊙ le) γ a
            ≡[ cong Tm (cong fib (Conᴹ.rest-⊙ Γ {γ = γ})) ]
          rest le' (Conᴹ.rest Γ le γ) (rest le γ a)

  variable
    A B : Tyᴹ Γ

  record Tmᴹ (Γ : Conᴹ) (A : Tyᴹ Γ) : Set where
    field
      at  : (γ : Tm (Conᴹ.obj Γ p)) → Tm (Tyᴹ.fib A γ)
      nat : ∀ {γ} → Tyᴹ.rest A le γ (at γ) ≡ at (Conᴹ.rest Γ le γ)

  variable
    σ τ θ : Subᴹ Δ Γ
    a b   : Tmᴹ Γ A

  top-uniq : {γ γ' : Tm `1} → γ ≡ γ'
  top-uniq {γ} {γ'} =
    trans (sym (unit-uniq .to-from γ)) (unit-uniq .to-from γ')

  cwfᴹ : FO-CwF.CwF
  cwfᴹ .C.sorts .Cˢ.Con = Conᴹ
  cwfᴹ .C.sorts .Cˢ.Sub = Subᴹ
  cwfᴹ .C.sorts .Cˢ.Ty = Tyᴹ
  cwfᴹ .C.sorts .Cˢ.Tm = Tmᴹ
  cwfᴹ .C.ctors .Cᶜ.id .Subᴹ.map γ = γ
  cwfᴹ .C.ctors .Cᶜ.id .Subᴹ.nat = refl
  cwfᴹ .C.ctors .Cᶜ._∘_ σ τ .Subᴹ.map γ =
    σ .Subᴹ.map (τ .Subᴹ.map γ)
  cwfᴹ .C.ctors .Cᶜ._∘_ σ τ .Subᴹ.nat =
    trans (σ .Subᴹ.nat) (cong (σ .Subᴹ.map) (τ .Subᴹ.nat))
  cwfᴹ .C.ctors .Cᶜ.id∘ = refl
  cwfᴹ .C.ctors .Cᶜ.∘id = refl
  cwfᴹ .C.ctors .Cᶜ.assoc = refl
  cwfᴹ .C.ctors .Cᶜ.∙ .Conᴹ.obj _ = `1
  cwfᴹ .C.ctors .Cᶜ.∙ .Conᴹ.rest _ _ = top
  cwfᴹ .C.ctors .Cᶜ.∙ .Conᴹ.rest-id = top-uniq
  cwfᴹ .C.ctors .Cᶜ.∙ .Conᴹ.rest-⊙ = top-uniq
  cwfᴹ .C.ctors .Cᶜ.ε .Subᴹ.map _ = top
  cwfᴹ .C.ctors .Cᶜ.ε .Subᴹ.nat = top-uniq
  cwfᴹ .C.ctors .Cᶜ.∃!ε = {!!}
  cwfᴹ .C.ctors .Cᶜ._[_]T A σ .Tyᴹ.fib γ =
    A .Tyᴹ.fib (σ .Subᴹ.map γ)
  cwfᴹ .C.ctors .Cᶜ._[_]T A σ .Tyᴹ.rest le γ a =
    coe (cong Tm (cong (A .Tyᴹ.fib) (σ .Subᴹ.nat)))
      (A .Tyᴹ.rest le (σ .Subᴹ.map γ) a)
  cwfᴹ .C.ctors .Cᶜ._[_]T A σ .Tyᴹ.rest-id = {!!}
  cwfᴹ .C.ctors .Cᶜ._[_]T A σ .Tyᴹ.rest-⊙ = {!!}
  cwfᴹ .C.ctors .Cᶜ.[id]T = {!!}
  cwfᴹ .C.ctors .Cᶜ.[∘]T = {!!}
  cwfᴹ .C.ctors .Cᶜ._[_] a σ .Tmᴹ.at γ = a .Tmᴹ.at (σ .Subᴹ.map γ)
  cwfᴹ .C.ctors .Cᶜ._[_] a σ .Tmᴹ.nat = {!!}
  cwfᴹ .C.ctors .Cᶜ.[id] = {!!}
  cwfᴹ .C.ctors .Cᶜ.[∘] = {!!}
  cwfᴹ .C.ctors .Cᶜ._▷_ Γ A .Conᴹ.obj p =
    Σ (Conᴹ.obj Γ p) (A .Tyᴹ.fib)
  cwfᴹ .C.ctors .Cᶜ._▷_ Γ A .Conᴹ.rest le w =
    pair (Conᴹ.rest Γ le (first w))
      (A .Tyᴹ.rest le (first w) (second w))
  cwfᴹ .C.ctors .Cᶜ._▷_ Γ A .Conᴹ.rest-id = {!!}
  cwfᴹ .C.ctors .Cᶜ._▷_ Γ A .Conᴹ.rest-⊙ = {!!}
  cwfᴹ .C.ctors .Cᶜ.p .Subᴹ.map w = first w
  cwfᴹ .C.ctors .Cᶜ.p .Subᴹ.nat = sym first-pair
  cwfᴹ .C.ctors .Cᶜ.q .Tmᴹ.at w = second w
  cwfᴹ .C.ctors .Cᶜ.q .Tmᴹ.nat = {!!}
  cwfᴹ .C.ctors .Cᶜ._,_ σ a .Subᴹ.map γ =
    pair (σ .Subᴹ.map γ) (a .Tmᴹ.at γ)
  cwfᴹ .C.ctors .Cᶜ._,_ σ a .Subᴹ.nat = {!!}
  cwfᴹ .C.ctors .Cᶜ.p∘, = {!!}
  cwfᴹ .C.ctors .Cᶜ.,∘ = {!!}
  cwfᴹ .C.ctors .Cᶜ.p,q = {!!}
  cwfᴹ .C.ctors .Cᶜ.q[,] = {!!}

  gatᴹ : FO-GAT.GAT-ToS
  gatᴹ .G.cwf = cwfᴹ
  gatᴹ .G.gat-ctors .Gᶜ.`1 = {!!}
  gatᴹ .G.gat-ctors .Gᶜ.`1[] = {!!}
  gatᴹ .G.gat-ctors .Gᶜ.unit-uniq = {!!}
  gatᴹ .G.gat-ctors .Gᶜ.top[] = {!!}
  gatᴹ .G.gat-ctors .Gᶜ.Σ = {!!}
  gatᴹ .G.gat-ctors .Gᶜ.Σ[] = {!!}
  gatᴹ .G.gat-ctors .Gᶜ.pair-proj = {!!}
  gatᴹ .G.gat-ctors .Gᶜ.U = {!!}
  gatᴹ .G.gat-ctors .Gᶜ.U[] = {!!}
  gatᴹ .G.gat-ctors .Gᶜ.El = {!!}
  gatᴹ .G.gat-ctors .Gᶜ.El[] = {!!}
  gatᴹ .G.gat-ctors .Gᶜ.Π = {!!}
  gatᴹ .G.gat-ctors .Gᶜ.Π[] = {!!}
  gatᴹ .G.gat-ctors .Gᶜ.lam-app = {!!}
  gatᴹ .G.gat-ctors .Gᶜ.lam[] = {!!}
  gatᴹ .G.gat-ctors .Gᶜ.Eq = {!!}
  gatᴹ .G.gat-ctors .Gᶜ.Eq[] = {!!}
  gatᴹ .G.gat-ctors .Gᶜ.refl-reflect = {!!}
  gatᴹ .G.gat-ctors .Gᶜ.Refl[] = {!!}
  gatᴹ .G.gat-ctors .Gᶜ.Πᴱ = {!!}
  gatᴹ .G.gat-ctors .Gᶜ.Πᴱ[] = {!!}
  gatᴹ .G.gat-ctors .Gᶜ.lam-appᴱ = {!!}
  gatᴹ .G.gat-ctors .Gᶜ.lamᴱ[] = {!!}

  sogatᴹ : FO-SOGAT.SOGAT-ToS
  sogatᴹ .S.gat = gatᴹ
  sogatᴹ .S.sogat-ctors .Sᶜ.Uᴿ = {!!}
  sogatᴹ .S.sogat-ctors .Sᶜ.Uᴿ[] = {!!}
  sogatᴹ .S.sogat-ctors .Sᶜ.elᴿ = {!!}
  sogatᴹ .S.sogat-ctors .Sᶜ.elᴿ[] = {!!}
  sogatᴹ .S.sogat-ctors .Sᶜ.Πᴿ = {!!}
  sogatᴹ .S.sogat-ctors .Sᶜ.lam-appᴿ = {!!}

  fo-psogat : FO.PSOGAT-ToS Φ
  fo-psogat .P.sogat = sogatᴹ
  fo-psogat .P.psogat-ctors .Pᶜ.In = {!!}
  fo-psogat .P.psogat-ctors .Pᶜ.In[] = {!!}
  fo-psogat .P.psogat-ctors .Pᶜ.In-prop = {!!}
  fo-psogat .P.psogat-ctors .Pᶜ.in⊤ = {!!}
  fo-psogat .P.psogat-ctors .Pᶜ.in-and-proj = {!!}
  fo-psogat .P.psogat-ctors .Pᶜ.Πᴾ = {!!}
  fo-psogat .P.psogat-ctors .Pᶜ.↑↓ = {!!}
  fo-psogat .P.psogat-ctors .Pᶜ.Πᴾᵁ = {!!}
  fo-psogat .P.psogat-ctors .Pᶜ.↑↓ᵁ = {!!}
  fo-psogat .P.psogat-ctors .Pᶜ.Πᴾᴿ = {!!}
  fo-psogat .P.psogat-ctors .Pᶜ.↑↓ᴿ = {!!}

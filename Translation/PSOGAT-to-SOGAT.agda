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
  open SO.SOGAT-ToS s
  open InPhaseAlg Φ

  -- What we will do is build a model of PSOGAT ToS in Psh(Φ) with *the object
  -- universe* for Ty/Tm.

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

  record Conᴹ : Set₁ where
    field
      obj  : Phase → Set
      rest : q ≤ p → obj p → obj q
      rest-id : {γ : obj p} → rest ≤-refl γ ≡ γ
      rest-⊙ : {γ : obj p} → rest (le' ⊙ le) γ ≡ rest le' (rest le γ)

  variable
    Γ Δ Θ : Conᴹ

  record Subᴹ (Δ Γ : Conᴹ) : Set where
    field
      map : Conᴹ.obj Δ p → Conᴹ.obj Γ p
      nat : ∀ {δ} → Conᴹ.rest Γ le (map δ) ≡ map (Conᴹ.rest Δ le δ)

  record Tyᴹ (Γ : Conᴹ) : Set where
    field
      fib  : Conᴹ.obj Γ p → Ty
      rest : (le : q ≤ p) (γ : Conᴹ.obj Γ p)
        → Tm (fib γ) → Tm (fib (Conᴹ.rest Γ le γ))
      rest-id : ∀ {γ : Conᴹ.obj Γ p} {a}
        → rest ≤-refl γ a ≡[ cong Tm (cong fib (Conᴹ.rest-id Γ {γ = γ})) ] a
      rest-⊙ : ∀ {γ : Conᴹ.obj Γ p} {a}
        → rest (le' ⊙ le) γ a
            ≡[ cong Tm (cong fib (Conᴹ.rest-⊙ Γ {γ = γ})) ]
          rest le' (Conᴹ.rest Γ le γ) (rest le γ a)

  variable
    A B : Tyᴹ Γ

  record Tmᴹ (Γ : Conᴹ) (A : Tyᴹ Γ) : Set where
    field
      at  : (γ : Conᴹ.obj Γ p) → Tm (Tyᴹ.fib A γ)
      nat : ∀ {γ} → Tyᴹ.rest A le γ (at γ) ≡ at (Conᴹ.rest Γ le γ)

  variable
    σ τ θ : Subᴹ Δ Γ
    a b   : Tmᴹ Γ A
    γ δ   : Conᴹ.obj Γ p

  top-uniqᴹ : {γ γ' : Tm `1} → γ ≡ γ'
  top-uniqᴹ {γ} {γ'} = trans (top-uniq γ) (sym (top-uniq γ'))

  opaque
    unfolding coe
    rest-nat : (A : Tyᴹ Γ) {γ γ' : Conᴹ.obj Γ p} (e : γ ≡ γ') {a : Tm (A .Tyᴹ.fib γ)}
      → A .Tyᴹ.rest le γ a
        ≡[ cong Tm (cong (A .Tyᴹ.fib) (cong (Conᴹ.rest Γ le) e)) ]
        A .Tyᴹ.rest le γ' (coe (cong Tm (cong (A .Tyᴹ.fib) e)) a)
    rest-nat A refl = refl

    Subᴹ≡ : {σ τ : Subᴹ Δ Γ}
      → (∀ {p} (γ : Conᴹ.obj Δ p)
      → σ .Subᴹ.map γ ≡ τ .Subᴹ.map γ)
      → σ ≡ τ
    Subᴹ≡ {σ = σ} {τ = τ} m with ifunext (λ p → funext (m {p}))
    ... | refl = refl

    Tmᴹ≡ : {a b : Tmᴹ Γ A}
      → (∀ {p} (γ : Conᴹ.obj Γ p) → a .Tmᴹ.at γ ≡ b .Tmᴹ.at γ)
      → a ≡ b
    Tmᴹ≡ {a = a} {b = b} m with ifunext (λ p → funext (m {p}))
    ... | refl = refl

    Tyᴹ≡ : {A B : Tyᴹ Γ}
      → (e-fib : ∀ {p} (γ : Conᴹ.obj Γ p) → A .Tyᴹ.fib γ ≡ B .Tyᴹ.fib γ)
      → (∀ {p q} (le : q ≤ p) (γ : Conᴹ.obj Γ p) (a : Tm (A .Tyᴹ.fib γ))
      → A .Tyᴹ.rest le γ a
          ≡[ cong Tm (e-fib (Conᴹ.rest Γ le γ)) ]
        B .Tyᴹ.rest le γ (coe (cong Tm (e-fib γ)) a))
      → A ≡ B
    Tyᴹ≡ = {!!}


    ap-at : (e1 : A ≡ B) (e2 : a ≡[ cong (Tmᴹ Γ) e1 ] b) (γ : Conᴹ.obj Γ p)
      → a .Tmᴹ.at γ ≡[ cong (λ T → Tm (T .Tyᴹ.fib γ)) e1 ] b .Tmᴹ.at γ
    ap-at refl refl γ = refl


  cwfᴹ : FO-CwF.CwF
  cwfᴹ .C.sorts .Cˢ.Con = Conᴹ
  cwfᴹ .C.sorts .Cˢ.Sub = Subᴹ
  cwfᴹ .C.sorts .Cˢ.Ty = Tyᴹ
  cwfᴹ .C.sorts .Cˢ.Tm = Tmᴹ
  cwfᴹ .C.ctors .Cᶜ.id .Subᴹ.map γ = γ
  cwfᴹ .C.ctors .Cᶜ.id .Subᴹ.nat = refl
  cwfᴹ .C.ctors .Cᶜ._∘_ σ τ .Subᴹ.map γ = σ .Subᴹ.map (τ .Subᴹ.map γ)
  cwfᴹ .C.ctors .Cᶜ._∘_ σ τ .Subᴹ.nat = trans (σ .Subᴹ.nat) (cong (σ .Subᴹ.map) (τ .Subᴹ.nat))
  cwfᴹ .C.ctors .Cᶜ.id∘ = refl
  cwfᴹ .C.ctors .Cᶜ.∘id = refl
  cwfᴹ .C.ctors .Cᶜ.assoc = refl
  cwfᴹ .C.ctors .Cᶜ.∙ .Conᴹ.obj _ = 𝟙
  cwfᴹ .C.ctors .Cᶜ.∙ .Conᴹ.rest _ _ = tt
  cwfᴹ .C.ctors .Cᶜ.∙ .Conᴹ.rest-id = refl
  cwfᴹ .C.ctors .Cᶜ.∙ .Conᴹ.rest-⊙ = refl
  cwfᴹ .C.ctors .Cᶜ.ε .Subᴹ.map _ = tt
  cwfᴹ .C.ctors .Cᶜ.ε .Subᴹ.nat = refl
  cwfᴹ .C.ctors .Cᶜ.∃!ε = Subᴹ≡ (λ _ → refl)
  cwfᴹ .C.ctors .Cᶜ._[_]T A σ .Tyᴹ.fib γ = A .Tyᴹ.fib (σ .Subᴹ.map γ)
  cwfᴹ .C.ctors .Cᶜ._[_]T A σ .Tyᴹ.rest le γ a =
    coe (cong Tm (cong (A .Tyᴹ.fib) (σ .Subᴹ.nat)))
      (A .Tyᴹ.rest le (σ .Subᴹ.map γ) a)
  cwfᴹ .C.ctors .Cᶜ._[_]T A σ .Tyᴹ.rest-id = splitl (A .Tyᴹ.rest-id)
  cwfᴹ .C.ctors .Cᶜ._[_]T A σ .Tyᴹ.rest-⊙ =
    splitl (splitr (transᴰ (A .Tyᴹ.rest-⊙) (rest-nat A (σ .Subᴹ.nat))))
  cwfᴹ .C.ctors .Cᶜ.[id]T = aux
    where
    opaque
      unfolding coe
      aux : cwfᴹ .C.ctors .Cᶜ._[_]T A (cwfᴹ .C.ctors .Cᶜ.id) ≡ A
      aux = refl
  cwfᴹ .C.ctors .Cᶜ.[∘]T = Tyᴹ≡ (λ _ → refl) λ le γ a → {!!}
  cwfᴹ .C.ctors .Cᶜ._[_] a σ .Tmᴹ.at γ = a .Tmᴹ.at (σ .Subᴹ.map γ)
  cwfᴹ .C.ctors .Cᶜ._[_] {A = A} a σ .Tmᴹ.nat = trans
    (cong (coe (cong Tm (cong (A .Tyᴹ.fib) (σ .Subᴹ.nat)))) (a .Tmᴹ.nat))
    (congᴰ (λ γ' → Tm (A .Tyᴹ.fib γ')) (a .Tmᴹ.at) (σ .Subᴹ.nat))
  cwfᴹ .C.ctors .Cᶜ.[id] = aux
    where
    opaque
      unfolding coe
      aux : cwfᴹ .C.ctors .Cᶜ._[_] a (cwfᴹ .C.ctors .Cᶜ.id) ≡[ cong (λ A' → Tmᴹ _ A') (cwfᴹ .C.ctors .Cᶜ.[id]T) ] a
      aux = refl
  cwfᴹ .C.ctors .Cᶜ.[∘] = Tmᴹ≡ {! !}
  cwfᴹ .C.ctors .Cᶜ._▷_ Γ A .Conᴹ.obj p = Σ[ γ ∈ Conᴹ.obj Γ p ] Tm (A .Tyᴹ.fib γ)
  cwfᴹ .C.ctors .Cᶜ._▷_ Γ A .Conᴹ.rest le (γ ,, a) = Conᴹ.rest Γ le γ ,, A .Tyᴹ.rest le γ a
  cwfᴹ .C.ctors .Cᶜ._▷_ Γ A .Conᴹ.rest-id = Σ≡ (Γ .Conᴹ.rest-id) (A .Tyᴹ.rest-id)
  cwfᴹ .C.ctors .Cᶜ._▷_ Γ A .Conᴹ.rest-⊙ = Σ≡ (Γ .Conᴹ.rest-⊙) (A .Tyᴹ.rest-⊙)
  cwfᴹ .C.ctors .Cᶜ.p .Subᴹ.map = proj₁
  cwfᴹ .C.ctors .Cᶜ.p .Subᴹ.nat = refl
  cwfᴹ .C.ctors .Cᶜ.q .Tmᴹ.at = proj₂
  cwfᴹ .C.ctors .Cᶜ.q {A = A} .Tmᴹ.nat {γ = γ} = reflᴰ
  cwfᴹ .C.ctors .Cᶜ._,_ σ a .Subᴹ.map γ = σ .Subᴹ.map γ ,, a .Tmᴹ.at γ
  cwfᴹ .C.ctors .Cᶜ._,_ σ a .Subᴹ.nat = Σ≡ (σ .Subᴹ.nat) (a .Tmᴹ.nat)
  cwfᴹ .C.ctors .Cᶜ.p∘, = refl
  cwfᴹ .C.ctors .Cᶜ.,∘ = Subᴹ≡ λ γ → Σ≡ refl (ap-at (Tyᴹ≡ (λ _ → refl) λ le γ₁ a₁ → {!  !}) refl γ)
  cwfᴹ .C.ctors .Cᶜ.p,q = refl
  cwfᴹ .C.ctors .Cᶜ.q[,] = Tmᴹ≡ λ γ → sym (undep (ap-at (Tyᴹ≡ (λ _ → refl) λ le γ₁ a₁ → {!  !}) refl γ))

  gatᴹ : FO-GAT.GAT-ToS
  gatᴹ .G.cwf = cwfᴹ
  gatᴹ .G.gat-ctors .Gᶜ.`1 .Tyᴹ.fib _ = `1
  gatᴹ .G.gat-ctors .Gᶜ.`1 .Tyᴹ.rest _ _ _ = top
  gatᴹ .G.gat-ctors .Gᶜ.`1 .Tyᴹ.rest-id = top-uniqᴹ
  gatᴹ .G.gat-ctors .Gᶜ.`1 .Tyᴹ.rest-⊙ = top-uniqᴹ
  gatᴹ .G.gat-ctors .Gᶜ.`1[] = {!!}
  gatᴹ .G.gat-ctors .Gᶜ.unit-uniq .to _ .Tmᴹ.at _ = top
  gatᴹ .G.gat-ctors .Gᶜ.unit-uniq .to _ .Tmᴹ.nat = top-uniqᴹ
  gatᴹ .G.gat-ctors .Gᶜ.unit-uniq .from _ = tt
  gatᴹ .G.gat-ctors .Gᶜ.unit-uniq .to-from _ = {!!}
  gatᴹ .G.gat-ctors .Gᶜ.unit-uniq .from-to _ = refl
  gatᴹ .G.gat-ctors .Gᶜ.top[] = {!!}
  gatᴹ .G.gat-ctors .Gᶜ.Σ A B .Tyᴹ.fib γ =
    Σ (A .Tyᴹ.fib γ) (λ x → B .Tyᴹ.fib (γ ,, x))
  gatᴹ .G.gat-ctors .Gᶜ.Σ A B .Tyᴹ.rest le γ w =
    pair (A .Tyᴹ.rest le γ (first w))
         (B .Tyᴹ.rest le (γ ,, first w) (second w))
  gatᴹ .G.gat-ctors .Gᶜ.Σ A B .Tyᴹ.rest-id = {!!}
  gatᴹ .G.gat-ctors .Gᶜ.Σ A B .Tyᴹ.rest-⊙ = {!!}
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
  gatᴹ .G.gat-ctors .Gᶜ.Eq s t .Tyᴹ.fib γ = Eq (s .Tmᴹ.at γ) (t .Tmᴹ.at γ)
  gatᴹ .G.gat-ctors .Gᶜ.Eq {A = A} s t .Tyᴹ.rest le γ x =
    refl-reflect .to
      (by (trans (sym (s .Tmᴹ.nat))
        (trans (cong (A .Tyᴹ.rest le γ) (refl-reflect .from x .witness)) (t .Tmᴹ.nat))))
  gatᴹ .G.gat-ctors .Gᶜ.Eq s t .Tyᴹ.rest-id = {!!}
  gatᴹ .G.gat-ctors .Gᶜ.Eq s t .Tyᴹ.rest-⊙ = {!!}
  gatᴹ .G.gat-ctors .Gᶜ.Eq[] = {!!}
  gatᴹ .G.gat-ctors .Gᶜ.refl-reflect = {!!}
  gatᴹ .G.gat-ctors .Gᶜ.Refl[] = {!!}
  gatᴹ .G.gat-ctors .Gᶜ.Πᴱ S B .Tyᴹ.fib γ = Πᴱ S (λ s → B s .Tyᴹ.fib γ)
  gatᴹ .G.gat-ctors .Gᶜ.Πᴱ S B .Tyᴹ.rest le γ g = lamᴱ (λ s → B s .Tyᴹ.rest le γ (g ∙ᴱ s))
  gatᴹ .G.gat-ctors .Gᶜ.Πᴱ S B .Tyᴹ.rest-id = {!!}
  gatᴹ .G.gat-ctors .Gᶜ.Πᴱ S B .Tyᴹ.rest-⊙ = {!!}
  gatᴹ .G.gat-ctors .Gᶜ.Πᴱ[] = {! refl!}
  gatᴹ .G.gat-ctors .Gᶜ.lam-appᴱ .to f .Tmᴹ.at γ = lamᴱ (λ s → f s .Tmᴹ.at γ)
  gatᴹ .G.gat-ctors .Gᶜ.lam-appᴱ .to f .Tmᴹ.nat = cong lamᴱ (funext (λ s → f s .Tmᴹ.nat))
  gatᴹ .G.gat-ctors .Gᶜ.lam-appᴱ .from t s .Tmᴹ.at γ = t .Tmᴹ.at γ ∙ᴱ s
  gatᴹ .G.gat-ctors .Gᶜ.lam-appᴱ .from t s .Tmᴹ.nat = cong (_∙ᴱ s) (t .Tmᴹ.nat)
  gatᴹ .G.gat-ctors .Gᶜ.lam-appᴱ .to-from _ = refl
  gatᴹ .G.gat-ctors .Gᶜ.lam-appᴱ .from-to _ = refl
  gatᴹ .G.gat-ctors .Gᶜ.lamᴱ[] = {!!}

  sogatᴹ : FO-SOGAT.SOGAT-ToS
  sogatᴹ .S.gat = gatᴹ
  sogatᴹ .S.sogat-ctors .Sᶜ.Uᴿ = {!!}
  sogatᴹ .S.sogat-ctors .Sᶜ.Uᴿ[] = {!!}
  sogatᴹ .S.sogat-ctors .Sᶜ.elᴿ = {!!}
  sogatᴹ .S.sogat-ctors .Sᶜ.elᴿ[] = {!!}
  sogatᴹ .S.sogat-ctors .Sᶜ.Πᴿ = {!!}
  sogatᴹ .S.sogat-ctors .Sᶜ.lam-appᴿ = {!!}

  psogatᴹ : FO.PSOGAT-ToS Φ
  psogatᴹ .P.sogat = sogatᴹ
  psogatᴹ .P.psogat-ctors .Pᶜ.In = {!!}
  psogatᴹ .P.psogat-ctors .Pᶜ.In[] = {!!}
  psogatᴹ .P.psogat-ctors .Pᶜ.In-prop = {!!}
  psogatᴹ .P.psogat-ctors .Pᶜ.in⊤ = {!!}
  psogatᴹ .P.psogat-ctors .Pᶜ.in-and-proj = {!!}
  psogatᴹ .P.psogat-ctors .Pᶜ.Πᴾ = {!!}
  psogatᴹ .P.psogat-ctors .Pᶜ.↑↓ = {!!}
  psogatᴹ .P.psogat-ctors .Pᶜ.Πᴾᵁ = {!!}
  psogatᴹ .P.psogat-ctors .Pᶜ.↑↓ᵁ = {!!}
  psogatᴹ .P.psogat-ctors .Pᶜ.Πᴾᴿ = {!!}
  psogatᴹ .P.psogat-ctors .Pᶜ.↑↓ᴿ = {!!}

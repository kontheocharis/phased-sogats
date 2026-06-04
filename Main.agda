module Main where

open import Data.Product using (Σ-syntax; proj₁; proj₂; _,_)
open import Data.Unit using (tt) renaming (⊤ to 𝟙)
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

    P : Set
    m n : P → Tm _
    X : S → Ty
    

  record GAT-ToSᶜ : Set₁ where
    field
      Σ : (A : Ty) → (Tm A → Ty) → Ty
      pair-proj : (Σ[ a ∈ Tm A ] Tm (F a)) ≃ Tm (Σ A F)

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
    syntax Πᴱ A (λ x → B) = [ x ∶ A ] ⇒ᴱ B

    top : Tm `1
    top = unit-uniq .to tt

    pair : (a : Tm A) → Tm (F a) → Tm (Σ A F)
    pair a b  = pair-proj .to (a , b)

    first : Tm (Σ A F) → Tm A
    first p = pair-proj .from p .proj₁

    second : (p : Tm (Σ A F)) → Tm (F (first p))
    second p = pair-proj .from p .proj₂

    _∙_ : Tm (Π a F) → (a : Tm (El a)) → Tm (F a)
    _∙_ = lam-app .from

    _∙ᴱ_ : Tm (Πᴱ S X) → (s : S) → Tm (X s)
    _∙ᴱ_ = lam-appᴱ .from

    lamᴱ : ((s : S) → Tm (X s)) → Tm (Πᴱ S X)
    lamᴱ = lam-appᴱ .to

    lamᴱ-appᴱ : lamᴱ m ∙ᴱ u ≡ m u
    lamᴱ-appᴱ = ap-$ (lam-appᴱ .from-to _) _

    infixr 3 _⇒_
    _⇒_ : Tm U → Ty → Ty
    A ⇒ B = Π A (λ _ → B)

    Iso : Tm U → Tm U → Ty
    Iso A B =
      from ∶ A ⇒ El B ⨾
      to ∶ B ⇒ El A ⨾
      from-to ∶ [ x ∶ B ] ⇒ Eq (from ∙ (to ∙ x)) x ⨾
      to-from ∶ [ x ∶ A ] ⇒ Eq (to ∙ (from ∙ x)) x ⨾
      `1

    iso-fwd : Tm (Iso a b) → Tm (El a) → Tm (El b)
    iso-fwd i x = first i ∙ x

    iso-bwd : Tm (Iso a b) → Tm (El b) → Tm (El a)
    iso-bwd i x = first (second i) ∙ x

    iso-fwd-bwd : iso-fwd a (iso-bwd a c) ≡ c
    iso-fwd-bwd {a = i} {c = x} = refl-reflect .from (first (second (second i)) ∙ x) .witness

    iso-bwd-fwd : iso-bwd a (iso-fwd a c) ≡ c
    iso-bwd-fwd {a = i} {c = x} = refl-reflect .from (first (second (second (second i))) ∙ x) .witness

  record SOGAT-ToSᶜ (gat : GAT-ToSᶜ) : Set₁ where
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


  record PSOGAT-ToSᶜ (Φ : PhaseAlg) (gat : GAT-ToSᶜ) (sogat : SOGAT-ToSᶜ gat) : Set₁ where
    open PhaseAlg Φ
    open GAT-ToSᶜ gat
    open SOGAT-ToSᶜ sogat
    field

      In : Phase → Set
      in⊤ : In ⊤
      Πᴾ : (p : Phase) → Tm U → Tm U
      Πᴾᴿ : (p : Phase) → Tm Uᴿ → Tm Uᴿ
      ↓↑ : (In t → Tm (El a)) ≃ Tm (El (Πᴾ t a))
      ↓↑ᴿ : (In t → Tm (El (elᴿ a))) ≃ Tm (El (elᴿ (Πᴾᴿ t a)))


record GAT-ToS : Set₁ where
  field
    gat-sorts : GAT-ToSˢ
  open GAT-ToSˢ gat-sorts public
  field
    gat-ctors : in-GAT-ToSˢ.GAT-ToSᶜ gat-sorts
  open in-GAT-ToSˢ.GAT-ToSᶜ gat-ctors public

record SOGAT-ToS : Set₁ where
  field
    gat : GAT-ToS
  open GAT-ToS gat public
  field
    sogat-ctors : in-GAT-ToSˢ.SOGAT-ToSᶜ gat-sorts gat-ctors
  open in-GAT-ToSˢ.SOGAT-ToSᶜ sogat-ctors public

record PSOGAT-ToS (Φ : PhaseAlg) : Set₁ where
  field
    sogat : SOGAT-ToS
  open SOGAT-ToS sogat public
  field
    psogat-ctors : in-GAT-ToSˢ.PSOGAT-ToSᶜ gat-sorts Φ gat-ctors sogat-ctors
  open in-GAT-ToSˢ.PSOGAT-ToSᶜ psogat-ctors public

-- I need to remove all this module noise 
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

  module _ (In : Phase → Tm Uᴿ) (in⊤ : Tm (El (elᴿ (In ⊤)))) where
  
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
      = pair (lamᴱ λ p → Πᴿ (first a ∙ᴱ p) (λ x → first (F ({! ?!})) ∙ᴱ p)) {! !}
    ps .PSG.sogat .SG.sogat-ctors .SGᶜ.lam-appᴿ = {!!}
    ps .PSG.psogat-ctors .PSGᶜ.In p = Tm (El (elᴿ (In p)))
    ps .PSG.psogat-ctors .PSGᶜ.in⊤ = in⊤
    ps .PSG.psogat-ctors .PSGᶜ.Πᴾ p X
      = pair (lamᴱ λ p' → first X ∙ᴱ (p ∧ p'))
        (pair (lamᴱ (λ p' → {! pair ? ? !})) top)
    ps .PSG.psogat-ctors .PSGᶜ.↓↑ = {! !}
    ps .PSG.psogat-ctors .PSGᶜ.Πᴾᴿ p X
      = pair (lamᴱ λ p' → first X ∙ᴱ (p ∧ p'))
        (pair {!!} top)
    ps .PSG.psogat-ctors .PSGᶜ.↓↑ᴿ = {!!}



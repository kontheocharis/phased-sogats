module ToS where

open import Data.Product using (Σ-syntax; proj₁; proj₂; _,_; _×_)
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

    first-pair : first (pair a b) ≡ a
    first-pair = cong proj₁ (pair-proj .from-to (_ , _))

    _∙_ : Tm (Π a F) → (a : Tm (El a)) → Tm (F a)
    _∙_ = lam-app .from

    lam : ((x : Tm (El a)) → Tm (F x)) → Tm (Π a F)
    lam = lam-app .to

    _∙ᴱ_ : Tm (Πᴱ S X) → (s : S) → Tm (X s)
    _∙ᴱ_ = lam-appᴱ .from

    lamᴱ : ((s : S) → Tm (X s)) → Tm (Πᴱ S X)
    lamᴱ = lam-appᴱ .to

    lamᴱ-appᴱ : lamᴱ m ∙ᴱ u ≡ m u
    lamᴱ-appᴱ = ap-$ (lam-appᴱ .from-to _) _

    lam-app∙ : lam f ∙ b ≡ f b
    lam-app∙ = ap-$ (lam-app .from-to _) _

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

    iso : (fwd : Tm (El a) → Tm (El b)) (bwd : Tm (El b) → Tm (El a))
          → ((x : Tm (El b)) → fwd (bwd x) ≡ x)
          → ((x : Tm (El a)) → bwd (fwd x) ≡ x)
          → Tm (Iso a b)
    iso fwd bwd fb bf =
      pair (lam fwd) (pair (lam bwd)
        (pair (lam λ x → refl-reflect .to
          (by (trans (cong (lam fwd ∙_) lam-app∙)
          (trans lam-app∙ (fb x)))))
        (pair (lam λ x → refl-reflect .to
          (by (trans (cong (lam bwd ∙_) lam-app∙)
          (trans lam-app∙ (bf x)))))
      top)))

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

    _∙ᴿ_ : Tm (El (Πᴿ a f)) → (x : Tm (El (elᴿ a))) → Tm (El (f x))
    _∙ᴿ_ = lam-appᴿ .from

    lamᴿ : ((x : Tm (El (elᴿ a))) → Tm (El (f x))) → Tm (El (Πᴿ a f))
    lamᴿ = lam-appᴿ .to


  record PSOGAT-ToSᶜ (Φ : PhaseAlg) (gat : GAT-ToSᶜ) (sogat : SOGAT-ToSᶜ gat) : Set₁ where
    open PhaseAlg Φ
    open GAT-ToSᶜ gat
    open SOGAT-ToSᶜ sogat
    field

      In : Phase → Set
      In-prop : (x y : In t) → x ≡ y
      in⊤ : In ⊤
      In-and-proj : (In t × In u) ≃ In (t ∧ u)

      Πᴾ : (p : Phase) → Tm U → Tm U
      Πᴾᴿ : (p : Phase) → Tm Uᴿ → Tm Uᴿ
      ↓↑ : (In t → Tm (El a)) ≃ Tm (El (Πᴾ t a))
      ↓↑ᴿ : (In t → Tm (El (elᴿ a))) ≃ Tm (El (elᴿ (Πᴾᴿ t a)))

    In-and : In t → In u → In (t ∧ u)
    In-and x y = In-and-proj .to (x , y)

    In-fst : In (t ∧ u) → In t
    In-fst z = In-and-proj .from z .proj₁

    In-snd : In (t ∧ u) → In u
    In-snd z = In-and-proj .from z .proj₂


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

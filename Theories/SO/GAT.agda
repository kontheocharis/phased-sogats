module Theories.SO.GAT where

open import Data.Product using (Σ-syntax; proj₁; proj₂; _,_)
open import Data.Unit using (tt) renaming (⊤ to 𝟙)
open import Utils hiding (⊤; _∧_)

postulate
  In-GAT-ToS : Prop

module GAT-ToS (_ : In-GAT-ToS) where

  postulate
    Ty : Set
    Tm : Ty → Set

  private variable
    S : Set
    t u v : S
    A B C : Ty
    F G H : Tm A → Ty
    a b c d : Tm A
    f g h : (x : Tm A) → Tm (F x)
    X : S → Ty
    Y : (s : S) → Tm (X s) → Ty
    fe : (s : S) → Tm (X s)

  postulate
    Σ : (A : Ty) → (Tm A → Ty) → Ty
    pair : (a : Tm A) → Tm (F a) → Tm (Σ A F)
    first : Tm (Σ A F) → Tm A
    second : (p : Tm (Σ A F)) → Tm (F (first p))
    first-pair : first (pair a b) ≡ a
  {-# REWRITE first-pair #-}
  postulate
    second-pair : second (pair a b) ≡ b
  {-# REWRITE second-pair #-}
  postulate
    pair-η : pair (first a) (second a) ≡ a
  {-# REWRITE pair-η #-}

  postulate
    `1 : Ty
    top : Tm `1
    top-uniq : (x : Tm `1) → x ≡ top

  postulate
    U : Ty
    El : Tm U → Ty

  postulate
    1ᵁ : Tm U
    topᵁ : Tm (El 1ᵁ)
    top-uniqᵁ : (x : Tm (El 1ᵁ)) → x ≡ topᵁ

  postulate
    Σᵁ : (a : Tm U) → (Tm (El a) → Tm U) → Tm U
    pairᵁ : (x : Tm (El a)) → Tm (El (f x)) → Tm (El (Σᵁ a f))
    firstᵁ : Tm (El (Σᵁ a f)) → Tm (El a)
    secondᵁ : (p : Tm (El (Σᵁ a f))) → Tm (El (f (firstᵁ p)))
    firstᵁ-pairᵁ : firstᵁ (pairᵁ a b) ≡ a
  {-# REWRITE firstᵁ-pairᵁ #-}
  postulate
    secondᵁ-pairᵁ : secondᵁ (pairᵁ a b) ≡ b
  {-# REWRITE secondᵁ-pairᵁ #-}
  postulate
    pairᵁ-η : (p : Tm (El (Σᵁ a f))) → pairᵁ (firstᵁ p) (secondᵁ p) ≡ p
  {-# REWRITE pairᵁ-η #-}

  postulate
    Π : (a : Tm U) → (Tm (El a) → Ty) → Ty
    lam : ((x : Tm (El a)) → Tm (F x)) → Tm (Π a F)
    _∙_ : Tm (Π a F) → (x : Tm (El a)) → Tm (F x)
    Π-β : (lam f) ∙ b ≡ f b
  {-# REWRITE Π-β #-}
  postulate
    Π-η : lam (λ x → a ∙ x) ≡ a
  {-# REWRITE Π-η #-}

  postulate
    Eq : Tm A → Tm A → Ty
    refl-reflect : ((a ≡ b) true) ≃ Tm (Eq a b)

  postulate
    Πᴱ : (S : Set) → (S → Ty) → Ty
    lamᴱ : ((s : S) → Tm (X s)) → Tm (Πᴱ S X)
    _∙ᴱ_ : Tm (Πᴱ S X) → (s : S) → Tm (X s)
    Πᴱ-β : (lamᴱ fe) ∙ᴱ t ≡ fe t
  {-# REWRITE Πᴱ-β #-}
  postulate
    Πᴱ-η : lamᴱ (λ s → a ∙ᴱ s) ≡ a
  {-# REWRITE Πᴱ-η #-}

  syntax Σ A (λ x → B) = x ∶ A ⨾ B
  syntax Π A (λ x → B) = [ x ∶ A ] ⇒ B
  syntax Πᴱ A (λ x → B) = [ x ∶ A ] ⇒ᴱ B

  pair-proj : (Σ[ a ∈ Tm A ] Tm (F a)) ≃ Tm (Σ A F)
  pair-proj .to (a , b) = pair a b
  pair-proj .from p = first p , second p
  pair-proj .to-from _ = refl
  pair-proj .from-to _ = refl

  opaque
    unfolding coe
    ap-pair : (e : t ≡ u)
      (eab : a ≡[ cong Tm (cong X e) ] b)
      (ecd : c ≡[ cong Tm (cong (λ (x , y) → Y x y) (Σ≡ e eab)) ] d)
      → pair a c ≡[ cong Tm (cong (λ s → Σ (X s) (Y s)) e) ] pair b d
    ap-pair refl refl refl = refl

  unit-uniq : 𝟙 ≃ Tm `1
  unit-uniq .to _ = top
  unit-uniq .from _ = tt
  unit-uniq .to-from x = sym (top-uniq x)
  unit-uniq .from-to _ = refl

  lam-app : ((x : Tm (El a)) → Tm (F x)) ≃ Tm (Π a F)
  lam-app .to = lam
  lam-app .from = _∙_
  lam-app .to-from _ = refl
  lam-app .from-to _ = refl

  lam-appᴱ : ((s : S) → Tm (X s)) ≃ Tm (Πᴱ S X)
  lam-appᴱ .to = lamᴱ
  lam-appᴱ .from = _∙ᴱ_
  lam-appᴱ .to-from _ = refl
  lam-appᴱ .from-to _ = refl

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

  iso-fwd-bwd : (i : Tm (Iso a b)) (x : Tm (El b))
              → iso-fwd i (iso-bwd i x) ≡ x
  iso-fwd-bwd i x = refl-reflect .from (first (second (second i)) ∙ x) .witness

  iso-bwd-fwd : (i : Tm (Iso a b)) (x : Tm (El a))
              → iso-bwd i (iso-fwd i x) ≡ x
  iso-bwd-fwd i x = refl-reflect .from (first (second (second (second i))) ∙ x) .witness

  iso : (fwd : Tm (El a) → Tm (El b)) (bwd : Tm (El b) → Tm (El a))
        → ((x : Tm (El b)) → fwd (bwd x) ≡ x)
        → ((x : Tm (El a)) → bwd (fwd x) ≡ x)
        → Tm (Iso a b)
  iso fwd bwd fb bf =
    pair (lam fwd) (pair (lam bwd)
      (pair (lam λ x → refl-reflect .to (by (fb x)))
      (pair (lam λ x → refl-reflect .to (by (bf x)))
    top)))

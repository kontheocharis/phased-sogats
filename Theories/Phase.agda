module Theories.Phase where

open import Utils hiding (⊤; _∧_)
open import Data.Product using (Σ-syntax; _,_)

private variable
  X : Set
  t u v : X

-- A phase algebra is basically just a meet semilattice.
record PhaseAlg : Set₁ where
  field
    Phase : Set
    _∧_ : Phase → Phase → Phase
    ⊤ : Phase
    ∧assoc : (t ∧ u) ∧ v ≡ t ∧ (u ∧ v)
    ∧comm : t ∧ u ≡ u ∧ t
    ∧idemp : t ∧ t ≡ t
    ∧⊤ : t ∧ ⊤ ≡ t

module InPhaseAlg (Φ : PhaseAlg) where
  open PhaseAlg Φ public

  -- Equipping PhaseAlg with a poset structure

  variable
    p q r : Phase

  -- The arrors of the poset
  infix 4 _≤_
  _≤_ : Phase → Phase → Prop
  q ≤ p = q ∧ p ≡ q

  ≤-refl : p ≤ p
  ≤-refl = ∧idemp

  infixr 9 _⊙_
  _⊙_ : r ≤ q → q ≤ p → r ≤ p
  _⊙_ {r} {q} {p} le' le =
    trans (sym (cong (_∧ p) le'))
    (trans ∧assoc
    (trans (cong (r ∧_) le) le'))

  -- Terminal object
  ≤-⊤ : p ≤ ⊤
  ≤-⊤ = ∧⊤

  -- Slice poset
  /_ : Phase → Set
  /_ p = Σ[ q ∈ Phase ] (q ≤ p) true

  /⊤ : / p
  /⊤ {p = p} = p , by ≤-refl

  /-map : q ≤ p → / q → / p
  /-map le (r , by le') = r , by (le' ⊙ le)

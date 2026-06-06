module Theories.Phase where

open import Utils hiding (⊤; _∧_)

private variable
  X : Set
  t u v : X

record PhaseAlg : Set₁ where
  field
    Phase : Set
    _∧_ : Phase → Phase → Phase
    ⊤ : Phase
    ∧assoc : (t ∧ u) ∧ v ≡ t ∧ (u ∧ v)
    ∧comm : t ∧ u ≡ u ∧ t
    ∧idemp : t ∧ t ≡ t
    ∧⊤ : t ∧ ⊤ ≡ t

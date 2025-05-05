{-# OPTIONS --guardedness #-}

open import Codata.Musical.Notation
open import Data.Nat using (ℕ)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
open import Level using (zero)

module Traces where

    Id : Set
    Id = ℕ

    Val : Set
    Val = ℕ

    State : Set
    State = Id → Val

    data Trace : Set where
        tnil : State → Trace
        tcons : State → ∞ Trace → Trace

    -- Definition of bisimilarity
    infix 4 _≈_

    data _≈_ : Rel Trace zero where
        tnil : ∀ {st} → (tnil st) ≈ (tnil st)
        tcons : ∀ {e tr₁ tr₂} → ∞ (♭ tr₁ ≈ ♭ tr₂) → (tcons e tr₁) ≈ (tcons e tr₂)

    
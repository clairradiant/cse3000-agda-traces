{-# OPTIONS --guardedness #-}

open import Codata.Musical.Notation
open import Data.Nat using (ℕ; suc; zero)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
import Level using (zero)
open import Data.Maybe using (Maybe)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_)

module Traces where

    Id : Set
    Id = ℕ

    Val : Set
    Val = ℕ

    State : Set
    State = Id → Val

    isTrue : Val → Bool
    isTrue zero = false
    isTrue (suc x) = true

    data FiniteTrace : Set where
        tnil : State → FiniteTrace
        tcons : State → FiniteTrace → FiniteTrace

    -- ##################
    -- # Musical Traces #
    -- ##################

    data Trace₁ : Set where
        tnil : State → Trace₁
        tcons : State → ∞ Trace₁ → Trace₁

    -- Definition of bisimilarity
    infix 4 _≈_

    data _≈_ : Rel Trace₁ Level.zero where
        tnil : ∀ {st} → (tnil st) ≈ (tnil st)
        tcons : ∀ {e tr₁ tr₂} → ∞ (♭ tr₁ ≈ ♭ tr₂) → (tcons e tr₁) ≈ (tcons e tr₂)

    setoid₁ : Setoid Level.zero Level.zero
    setoid₁ = record
        { Carrier = Trace₁
        ; _≈_ = _≈_
        ; isEquivalence = record
            {   refl = refl
            ;   sym = sym
            ;   trans = trans
            }
        }
        where
            refl : Reflexive _≈_
            refl {tnil x} = tnil
            refl {tcons x x₁} = tcons (♯ refl)

            sym : Symmetric _≈_
            sym tnil = tnil
            sym (tcons x) = tcons (♯ sym (♭ x))

            trans : Transitive _≈_
            trans tnil tnil = tnil
            trans (tcons x) (tcons x₁) = tcons (♯ trans (♭ x) ((♭ x₁)))

    -- Functions for forcing a trace to a non-coinductive trace or the trace's final state
    {-# NON_TERMINATING #-}
    force : Trace₁ → FiniteTrace
    force (tnil st) = tnil st
    force (tcons st tr) = tcons st (force (♭ tr))

    {-# NON_TERMINATING #-}
    final : Trace₁ → State
    final (tnil st) = st
    final (tcons _ tr) = final (♭ tr)

    -- #############################
    -- # Coinductive Record Traces #1
    -- #############################

    record Trace₂ : Set where
        coinductive
        constructor tcons
        field
            hd : State
            tl : Maybe Trace₂

    record Trace₃ : Set where
        coinductive
        constructor mkTrace
        field
            t : Maybe (State × Trace₃)

    
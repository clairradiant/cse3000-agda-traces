{-# OPTIONS --guardedness #-}

open import Codata.Musical.Notation
open import Data.Nat using (ℕ; suc; zero)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive; Substitutive)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; subst₂) renaming (sym to eqSym; trans to eqTrans)
import Level using (zero)

open import work.Language

module work.MusicalTraces where
    data FiniteTrace : Set where
        tnil : State → FiniteTrace
        tcons : State → FiniteTrace → FiniteTrace

    -- ##################
    -- # Musical Traces #
    -- ##################
    module Trace₁ where
        open Codata.Musical.Notation

        data Trace₁ : Set where
            tnil : State → Trace₁
            tcons : State → ∞ Trace₁ → Trace₁

        -- Definition of bisimilarity
        infix 4 _≈_

        data _≈_ : Rel Trace₁ Level.zero where
            tnil : ∀ {st} → (tnil st) ≈ (tnil st)
            tcons : ∀ {st tr₁ tr₂} → ∞ (♭ tr₁ ≈ ♭ tr₂) → (tcons st tr₁) ≈ (tcons st tr₂)

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

        -- Functions for forcing a trace to a non-coinductive trace or the trace's final state (usable for finite traces only)
        {-# NON_TERMINATING #-}
        force : Trace₁ → FiniteTrace
        force (tnil st) = tnil st
        force (tcons st tr) = tcons st (force (♭ tr))

        {-# NON_TERMINATING #-}
        final : Trace₁ → State
        final (tnil st) = st
        final (tcons _ tr) = final (♭ tr)

{-# OPTIONS --sized-types #-}

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive; Substitutive)
open import Level using (zero)
open import Size
open import Codata.Sized.Thunk

open import nakata.Language

module nakata.SizedTraces where
    data FiniteTrace : Set where
        tnil : State → FiniteTrace
        tcons : State → FiniteTrace → FiniteTrace

    -- ##################
    -- # Sized Traces   #
    -- ##################
    module Trace₄ where
        data Trace₄ (i : Size) : Set where
            tnil : State → Trace₄ i
            tcons : State 
                → Thunk Trace₄ i 
                → Trace₄ i

        fromFinite : FiniteTrace → Trace₄ ∞
        fromFinite (tnil x) = tnil x
        fromFinite (tcons x y) = tcons x (λ where .force → fromFinite y)

        data Bisim (i : Size) : Rel (Trace₄ ∞) Level.zero where
            tnil : ∀ {st} → Bisim i (tnil st) (tnil st)
            tcons : ∀ {st tr₁ tr₂} 
                → Thunk (λ s → Bisim s (force tr₁) (force tr₂)) i 
                → Bisim i (tcons st tr₁) (tcons st tr₂)


        setoid₄ : Size → Setoid Level.zero Level.zero
        setoid₄ i = record
            { Carrier = Trace₄ ∞
            ; _≈_ = Bisim i
            ; isEquivalence = record
                {   refl = refl
                ;   sym = sym
                ;   trans = trans
                }
            }
            where
                refl : ∀ {i} → Reflexive (Bisim i)
                refl {_} {tnil x} = tnil
                refl {_} {tcons x y} = tcons λ where .force → refl

                sym : ∀ {i} → Symmetric (Bisim i)
                sym tnil = tnil
                sym (tcons x) = tcons (λ where .force → sym (force x))

                trans : ∀ {i} → Transitive (Bisim i)
                trans tnil tnil = tnil
                trans (tcons x) (tcons y) = tcons λ where .force → trans (force x) (force y)

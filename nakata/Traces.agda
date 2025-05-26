{-# OPTIONS --guardedness #-}

open import Codata.Musical.Notation
open import Data.Nat using (ℕ; suc; zero)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; subst₂) renaming (sym to eqSym; trans to eqTrans)
import Level using (zero)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Maybe.Properties
open import Data.Bool using (Bool; true; false)
open import Data.Product
open import Data.Sum
open import Function.Base using (case_of_)
open import Relation.Nullary using (contradiction)

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
    module Trace₁ where
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

    -- #############################
    -- # Coinductive Record Traces
    -- #############################
    module Trace₂ where
        mutual
            data rTrace₂ : Set where
                tnil : State → rTrace₂
                tcons : State → Trace₂ → rTrace₂

            record Trace₂ : Set where
                coinductive
                constructor mkTr
                field
                    out : rTrace₂

        open Trace₂

        mutual
            data _r≈_ : Rel rTrace₂ Level.zero where
                tnil : ∀ {st} → (tnil st) r≈ (tnil st)
                tcons : ∀ {st tr₁ tr₂} → tr₁ ≈ tr₂ → (tcons st tr₁) r≈ (tcons st tr₂)

            record _≈_ (tr₁ tr₂ : Trace₂) : Set where
                coinductive
                constructor mkBisim
                field
                    p : (out tr₁) r≈ (out tr₂)

        setoid₂ : Setoid Level.zero Level.zero
        setoid₂ = record
            { Carrier = Trace₂
            ; _≈_ = _≈_
            ; isEquivalence = record
                {   refl = refl
                ;   sym = sym
                ;   trans = trans
                }
            }
            where
                refl : Reflexive _≈_
                refl {x} ._≈_.p = rrefl
                    where
                        rrefl : Reflexive _r≈_
                        rrefl {tnil x} = tnil
                        rrefl {tcons x x₁} = tcons refl


                sym : Symmetric _≈_
                sym h ._≈_.p = rsym (h ._≈_.p)
                    where
                        rsym : Symmetric _r≈_
                        rsym tnil = tnil
                        rsym (tcons x) = tcons (sym x)

                trans : Transitive _≈_
                trans x y ._≈_.p = rtrans (x ._≈_.p) (y ._≈_.p)
                    where
                        rtrans : Transitive _r≈_
                        rtrans tnil tnil = tnil
                        rtrans (tcons x) (tcons y) = tcons (trans x y)

        


    module Trace₃ where
        record Trace₃ : Set where
            coinductive
            constructor mkTr
            field
                hd : State
                tl : Maybe Trace₃

        open Trace₃

        record _≈_ (tr₁ tr₂ : Trace₃) : Set where
            coinductive
            field
                hd : hd tr₁ ≡ hd tr₂
                tl : (tl tr₁ ≡ nothing × tl tr₂ ≡ nothing)
                     ⊎
                     ∃ {A = (Trace₃ × Trace₃)} λ x → (
                        tl tr₁ ≡ just (proj₁ x)
                        ×
                        tl tr₂ ≡ just (proj₂ x)
                        ×
                        (proj₁ x) ≈ (proj₂ x))

        setoid₃ : Setoid Level.zero Level.zero
        setoid₃ = record
            { Carrier = Trace₃
            ; _≈_ = _≈_
            ; isEquivalence = record
                {   refl = refl
                ;   sym = sym
                ;   trans = trans
                }
            }
            where
                refl : Reflexive _≈_
                refl ._≈_.hd = _≡_.refl
                refl {x} ._≈_.tl with (tl x)
                ... | nothing = inj₁ (_≡_.refl , _≡_.refl)
                ... | (just tl) = inj₂ ((tl , tl) , _≡_.refl , (_≡_.refl , refl)) 

                sym : Symmetric _≈_
                sym x ._≈_.hd = eqSym (_≈_.hd x)
                sym {a} {b} x ._≈_.tl with (tl a) in eq | (tl b) in eq₁
                ... | nothing | nothing = inj₁ (_≡_.refl , _≡_.refl)
                ... | nothing | (just b₁) with _≈_.tl x
                ...                       | inj₁ (_ , snd)                      rewrite eq₁ = contradiction snd (λ ())
                ...                       | inj₂ (_ , (fst , _))                rewrite eq = contradiction fst (λ ())
                sym x ._≈_.tl | (just a₁) | nothing with _≈_.tl x
                ...                       | inj₁ (fst , _)                      rewrite eq = contradiction fst λ ()
                ...                       | inj₂ (_ , (_ , (fst , _)))          rewrite eq₁ = contradiction fst (λ ())
                sym x ._≈_.tl | (just a₁) | (just b₁) with (_≈_.tl x)
                ...                       | inj₁ (fst , _)                      rewrite eq = contradiction fst (λ ())
                ...  | inj₂ (_ , a₁≡left , b₁≡right , next)                     rewrite eq rewrite eq₁ = 
                    let 
                        t = just-injective a₁≡left 
                        t₂ = just-injective b₁≡right

                        t₃ : a₁ ≈ b₁
                        t₃ = subst₂ _≈_ (eqSym t) (eqSym t₂) next
                    in
                        inj₂ ((b₁ , a₁) , (_≡_.refl , (_≡_.refl , sym t₃)))

                trans : Transitive _≈_
                trans i≈j j≈k ._≈_.hd = eqTrans (_≈_.hd i≈j) (_≈_.hd j≈k)
                trans {i} {j} {k} i≈j j≈k ._≈_.tl with (tl i) in eq₁ | (tl j) in eq₂
                ... | nothing | nothing with (tl k) in eq₃
                ...                     | nothing = inj₁ (_≡_.refl , _≡_.refl)
                ...                     | (just c₁) with (_≈_.tl j≈k)
                ...                             | inj₁ (_ , a) rewrite eq₃ = contradiction a (λ ())
                ...                             | inj₂ (_ , a , _) rewrite eq₂ = contradiction a λ ()
                trans i≈j j≈k ._≈_.tl | nothing | (just b₁) with (_≈_.tl i≈j)
                ...                     | inj₁ (_ , snd)                      rewrite eq₂ = contradiction snd (λ ())
                ...                     | inj₂ (_ , (fst , _))                rewrite eq₁ = contradiction fst (λ ())
                trans i≈j j≈k ._≈_.tl | (just a₁) | nothing with (_≈_.tl i≈j)
                ...                     | inj₁ (fst , _)                      rewrite eq₁ = contradiction fst λ ()
                ...                     | inj₂ (_ , (_ , (fst , _)))          rewrite eq₂ = contradiction fst (λ ())
                trans {i} {j} {k} i≈j j≈k ._≈_.tl | (just a₁) | (just b₁) with (tl k) in eq₃
                ...                     | nothing with (_≈_.tl j≈k)
                ...                             | inj₁ (fst , _) rewrite eq₂ = contradiction fst (λ ())
                ...                             | inj₂ (_ , (_ , (fst , _))) rewrite eq₃ = contradiction fst (λ ())
                trans {i} {j} {k} i≈j j≈k ._≈_.tl | (just a₁) | (just b₁) | (just c₁) with (_≈_.tl i≈j) | (_≈_.tl j≈k)
                ...                                     | inj₁ (fst , _) | _     rewrite eq₁ = contradiction fst (λ ())
                ...                                     | inj₂ _      | inj₁ (fst , _) rewrite eq₂ = contradiction fst (λ ())
                ...                                     | inj₂ (_ , (fst , (snda , sndb))) | inj₂ (_ , (fst2 , (snda2 , sndb2))) rewrite eq₁ rewrite eq₂ rewrite eq₃ =     
                    let
                        t = just-injective fst
                        t₂ = just-injective snda
                        t₃ = just-injective fst2
                        t₄ = just-injective snda2

                        tli≈tlj : a₁ ≈ b₁
                        tli≈tlj = subst₂ _≈_ (eqSym t) (eqSym t₂) sndb

                        tlj≈tlk : b₁ ≈ c₁
                        tlj≈tlk = subst₂ _≈_ (eqSym t₃) (eqSym t₄) sndb2
                    in
                        inj₂ ((a₁ , c₁) , _≡_.refl , (_≡_.refl , trans tli≈tlj tlj≈tlk))


        

    
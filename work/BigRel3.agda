{-# OPTIONS --guardedness #-}

open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; subst) renaming (trans to eqTrans; sym to eqSym)
open import Codata.Musical.Notation
open import Data.Nat using (ℕ; zero; suc; _<?_)
open import Function.Base using (case_of_)
open import Data.Nat using (_+_)
open import Relation.Nullary using (contradiction)
open import Relation.Nullary.Decidable
open import Relation.Binary.Bundles using (Setoid)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product
open import Data.Sum

open import work.GuardedTraces
open import work.Language

open Trace₃

-- Note: Work on this was abandoned early on due to the difficulty of working with Trace₃, but the module is kept here for completeness.
module work.BigRel3 where
    open Trace₃.Trace₃

    mutual
        data exec : (s : Stmt) → (st : State) → (tr : Trace₃) → Set where
            execSkip : {st : State}
                → exec Sskip st (mkTr st nothing)

            execAssign : {id : Id} {a : Expr} {st : State} {tr : Trace₃}
                → exec (Sassign id a) st (mkTr st (just (mkTr (update id (a st) st) nothing)))

            execSeq : {s₁ s₂ : Stmt} {st : State} (tr tr′ : Trace₃) 
                → exec s₁ st tr 
                → execseq s₂ tr tr′
                → exec (Sseq s₁ s₂) st tr′

            execIfThenElseTrue : {c : Expr} {t : Stmt} {st : State} {tr : Trace₃} (e : Stmt)  
                → isTrue (c st) ≡ true 
                → execseq t (mkTr st (just (mkTr st nothing))) tr
                → exec (Sifthenelse c t e) st tr

            execIfThenElseFalse : {c : Expr} {e : Stmt} {st : State} {tr : Trace₃} (t : Stmt) 
                → isTrue (c st) ≡ false 
                → execseq e (mkTr st (just (mkTr st nothing))) tr
                → exec (Sifthenelse c t e) st tr

            execWhileFalse : {c : Expr} {st : State} {tr : Trace₃} (b : Stmt)
                → isTrue (c st) ≡ false
                → exec (Swhile c b) st (mkTr st (just (mkTr st nothing)))

            execWhileLoop : {c : Expr} {b : Stmt} {st : State} (tr tr′ : Trace₃)
                → (isTrue (c st)) ≡ true 
                → execseq b (mkTr st (just (mkTr st nothing))) tr
                → execseq (Swhile c b) tr tr′
                → exec (Swhile c b) st tr′

        record execseq (s : Stmt) (tr₁ tr₂ : Trace₃) : Set where
            coinductive
            field
                p :
                    ∃ (λ st → (tr₁ ≈ mkTr st nothing) × (exec s st tr₂)) -- "nil" case
                    ⊎
                    ∃ {A = State × (Trace₃ × Trace₃)} λ (st , (tr₃ , tr₄)) → -- "cons" case
                            ((tr₁ ≈ mkTr st ((just tr₃))) × (tr₂ ≈ mkTr st (just tr₄))) 
                        × 
                            execseq s tr₃ tr₄

    add1 : Expr
    add1 x = x 0 + 1

    startState : State
    startState = λ {0 → 0 ; _ → 42}

    next : State → State
    next st = update 0 (add1 st) st

    -- open Trace₂.Trace₂

    -- Record of what didn't work
    -- incrementingFrom : State → Trace₂
    -- incrementingFrom st .t = just (st , (incrementingFrom (next st)))

    -- incrementing : Trace₂
    -- incrementing = incrementingFrom startState

    -- test : incrementing ≈ incrementing
    -- test = tcons _≡_.refl _≡_.refl {!   !}

    open Trace₃.Trace₃

    incrementingFrom : State → Trace₃
    incrementingFrom st .hd = st
    incrementingFrom st .tl = just (incrementingFrom (next st))

    incrementing : Trace₃
    incrementing = incrementingFrom startState

    test : incrementing ≈ incrementing
    test = forever startState
        where
        forever : (st : State) → (incrementingFrom st) ≈ (incrementingFrom st)
        forever st ._≈_.hd = _≡_.refl
        forever st ._≈_.tl = inj₂ (((incrementingFrom (next st)) , (incrementingFrom (next st))) , 
            (_≡_.refl , (_≡_.refl , (forever (next st)))))


    execseqDeterministic₀ : {s : Stmt}
        → ({st : State} {tr₁ tr₂ : Trace₃} → exec s st tr₁ → exec s st tr₂ → tr₁ ≈ tr₂) 
        → ({tr₁ tr₂ tr₃ tr₄ : Trace₃} → tr₁ ≈ tr₂ → execseq s tr₁ tr₃ → execseq s tr₂ tr₄ → tr₃ ≈ tr₄)
    -- execseqDeterministic₀ h tnil              (execseqNil ex₁)         (execseqNil ex₂)         = h ex₁ ex₂
    -- execseqDeterministic₀ h (tcons tr₁′≈tr₂′) (execseqCons _ _ _ tr₁⇒tr₃) (execseqCons _ _ _ tr₂⇒tr₄) = tcons (♯ execseqDeterministic₀ h (♭ tr₁′≈tr₂′) (♭ tr₁⇒tr₃) (♭ tr₂⇒tr₄))
    execseqDeterministic₀ h {tr₁} {tr₂} {tr₃} {tr₄} a b c ._≈_.hd with (execseq.p b) | (execseq.p c)
    ... | inj₁ (ab , abc , abcd) | inj₁ (bc , bcd , bcde) = 
        let
            t : hd tr₁ ≡ ab
            t = _≈_.hd abc

            t₂ : hd tr₂ ≡ bc
            t₂ = _≈_.hd bcd

            t₃ : bc ≡ ab
            t₃ = eqTrans (eqSym t₂) (eqTrans (eqSym (_≈_.hd a)) t)
        in
            _≈_.hd (h abcd (subst (λ x → exec _ x tr₄) t₃ bcde))
    execseqDeterministic₀ h {tr₁} {tr₂} {tr₃} {tr₄} a b c ._≈_.tl with (_≈_.tl a) | (execseq.p b) | (execseq.p c)
    ... | inj₂ ((aaa , aaaa) , (bbb , (bbbb , bbbbb))) | inj₂ ((ab , (abb , abbb)) , (abc , abcc) , abcd) | inj₂ (bc , bcd , bcde) = 
        let
            t = {!   !}
        in
            inj₂ ((tr₁ , tr₂) , ({!   !} , ({!   !} , {!   !})))
    -- execseqDeterministic₀ h a b c ._≈_.tl with (_≈_.hd a) | (_≈_.tl a) | (execseq.p b) | (execseq.p c)
    -- ... | aa | bb | inj₁ (fst , _ , ex₁) | inj₁ (fst2 , _ , ex₂) = h ex₁ {!   !}
    -- ... | _ | _ | _ | _ = {!   !}

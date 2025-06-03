{-# OPTIONS --sized-types #-}

open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Nat using (ℕ; zero; suc; _<?_)
open import Function.Base using (case_of_)
open import Data.Nat using (_+_)
open import Relation.Binary.Bundles using (Setoid)
open import Size
open import Codata.Sized.Thunk

open import nakata.Language
open import nakata.SizedTraces

open Trace₄

module nakata.BigRel4 where
    mutual
        data exec : Stmt → State → Trace₄ ∞ → Set where
            execSkip : {st : State}
                → exec Sskip st (tnil st)

            execAssign : {id : Id} {a : Expr} {st : State} {tr : Trace₄ ∞}
                → Bisim ∞ tr (fromFinite (tcons st (tnil st)))
                → exec (Sassign id a) st tr

            execSeq : {s₁ s₂ : Stmt} {st : State} (tr tr′ : Trace₄ ∞) 
                → exec s₁ st tr 
                → execseq ∞ s₂ tr tr′ 
                → exec (Sseq s₁ s₂) st tr′

            execIfThenElseTrue : {c : Expr} {t : Stmt} {st : State} {tr : Trace₄ ∞} (e : Stmt)  
                → isTrue (c st) ≡ true 
                → execseq ∞ t (fromFinite (tcons st (tnil st))) tr 
                → exec (Sifthenelse c t e) st tr

            execIfThenElseFalse : {c : Expr} {e : Stmt} {st : State} {tr : Trace₄ ∞} (t : Stmt) 
                → isTrue (c st) ≡ false 
                → execseq ∞ e (fromFinite (tcons st (tnil st))) tr 
                → exec (Sifthenelse c t e) st tr

            execWhileFalse : {c : Expr} {st : State} {tr : Trace₄ ∞}
                → (b : Stmt)
                → isTrue (c st) ≡ false
                → Bisim ∞ tr (fromFinite (tcons st (tnil st)))
                → exec (Swhile c b) st tr

            execWhileLoop : {c : Expr} {b : Stmt} {st : State} (tr tr′ : Trace₄ ∞)
                → (isTrue (c st)) ≡ true 
                → execseq ∞ b (fromFinite (tcons st (tnil st))) tr 
                → execseq ∞ (Swhile c b) tr tr′ 
                → exec (Swhile c b) st tr′

        data execseq : Size → Stmt → Trace₄ ∞ → Trace₄ ∞ → Set where
            execseqNil : {i : Size} {st : State} {s : Stmt} {tr : Trace₄ ∞} 
                → exec s st tr 
                → execseq i s (tnil st) tr
                
            execseqCons : {i : Size} {s : Stmt} (st : State) (tr tr′ : Thunk Trace₄ ∞) 
                → Thunk (λ i → execseq i s (force tr) (force tr′)) i
                → execseq i s (tcons st tr) (tcons st tr′)

    startState : State
    startState = λ {0 → 0 ; _ → 42}

    module exloop where
        loopforevertrace : ∀ {i} → Trace₄ i
        loopforevertrace = tcons startState (λ where .force → loopforevertrace)

        exloopforever : exec (Swhile (λ _ → 1) Sskip) startState loopforevertrace
        exloopforever = execWhileLoop 
            (fromFinite (tcons startState (tnil startState))) 
            loopforevertrace 
            _≡_.refl 
            (execseqCons _ _ _ λ where .force → execseqNil execSkip) 
            {! forever  !}
            -- (execseqCons _ _ _ (λ where .force → execseqNil exloopforever))
            where
                forever : ∀ {i} → execseq i (Swhile (λ _ → 1) Sskip) (tcons startState (λ { .force → fromFinite (tnil startState) })) loopforevertrace
                forever = execseqCons _ _ _ λ where .force → execseqNil exloopforever



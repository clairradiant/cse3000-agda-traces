{-# OPTIONS --sized-types #-}

open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat using (_+_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Nullary using (contradiction)

open import Size
open import Codata.Sized.Thunk

open import work.Language
open import work.SizedTraces

open Trace₄

module work.BigRel4 where
    mutual
        data exec : Size → Stmt → State → Trace₄ ∞ → Set where
            execSkip : ∀ {i} {st : State}
                → exec i Sskip st (tnil st)

            execAssign : ∀ {i} {id : Id} {a : Expr} {st : State} {tr : Trace₄ ∞}
                → Bisim ∞ tr (fromFinite (tcons st (tnil (update id (a st) st))))
                → exec i (Sassign id a) st tr

            execSeq : ∀ {i} {s₁ s₂ : Stmt} {st : State} (tr tr′ : Trace₄ ∞) 
                → exec i s₁ st tr 
                → execseq i s₂ tr tr′ 
                → exec i (Sseq s₁ s₂) st tr′

            execIfThenElseTrue : ∀ {i} {c : Expr} {t : Stmt} {st : State} {tr : Trace₄ ∞} (e : Stmt)  
                → isTrue (c st) ≡ true 
                → execseq i t (fromFinite (tcons st (tnil st))) tr 
                → exec i (Sifthenelse c t e) st tr

            execIfThenElseFalse : ∀ {i} {c : Expr} {e : Stmt} {st : State} {tr : Trace₄ ∞} (t : Stmt) 
                → isTrue (c st) ≡ false 
                → execseq i e (fromFinite (tcons st (tnil st))) tr 
                → exec i (Sifthenelse c t e) st tr

            execWhileFalse : ∀ {i} {c : Expr} {st : State} {tr : Trace₄ ∞}
                → (b : Stmt)
                → isTrue (c st) ≡ false
                → Bisim ∞ tr (fromFinite (tcons st (tnil st)))
                → exec i (Swhile c b) st tr 

            execWhileLoop : ∀ {i} {c : Expr} {b : Stmt} {st : State} (tr tr′ : Trace₄ ∞)
                → (isTrue (c st)) ≡ true 
                → execseq i b (fromFinite (tcons st (tnil st))) tr 
                → execseq i (Swhile c b) tr tr′ 
                → exec i (Swhile c b) st tr′

        data execseq : Size → Stmt → Trace₄ ∞ → Trace₄ ∞ → Set where
            execseqNil : {i : Size} {st : State} {s : Stmt} {tr : Trace₄ ∞} 
                → exec i s st tr 
                → execseq i s (tnil st) tr
                
            execseqCons : {i : Size} {s : Stmt} (st : State) (tr tr′ : Thunk Trace₄ ∞) 
                → Thunk (λ i → execseq i s (force tr) (force tr′)) i
                → execseq i s (tcons st tr) (tcons st tr′)

    open Setoid (setoid₄ ∞)

    module examples where
        -- Common definitions
        startState : State
        startState = λ {0 → 0 ; _ → 42}

        -- Proof tree of a program that loops forever
        module loopForever where
            loopforevertrace : ∀ {i} → Trace₄ i
            loopforevertrace = tcons startState (λ where .force → loopforevertrace)

            exloopforever : ∀ {i} → exec i (Swhile (λ _ → 1) Sskip) startState loopforevertrace
            exloopforever = execWhileLoop 
                (fromFinite (tcons startState (tnil startState))) 
                loopforevertrace 
                _≡_.refl 
                (execseqCons _ _ _ λ where .force → execseqNil execSkip) 
                (execseqCons _ _ _ λ where .force → execseqNil exloopforever)

    
        -- Proof tree of a program generating the naturals (exloopincrementing)
        -- As well as a proof the trace actually does this (incrementingAlwaysIncrements)
        module increasing where
            add1 : Expr
            add1 x = x 0 + 1

            next : State → State
            next st = update 0 (add1 st) st

            incrementingFrom : ∀ {i} → State → Trace₄ i
            incrementingFrom st = tcons st λ where .force → tcons st (λ where .force → incrementingFrom (next st))

            incrementingtrace : Trace₄ ∞
            incrementingtrace = incrementingFrom startState

            exloopincrementing : exec ∞ (Swhile (λ _ → 1) (Sassign 0 add1)) startState incrementingtrace
            exloopincrementing = forever startState
                where
                    forever : ∀ {i} → (st : State) → exec i (Swhile (λ _ → 1) (Sassign 0 add1)) st (incrementingFrom st)
                    forever st = execWhileLoop (fromFinite (tcons st (tcons st (tnil (next st))))) _ _≡_.refl
                        (execseqCons _ _ _ λ where .force → execseqNil (execAssign refl)) 
                        (execseqCons _ _ _ λ where .force → execseqCons _ _ _ λ where .force → execseqNil (forever (next st)))

            data increasing : Size → Id → Val → Trace₄ ∞ → Set where
                increasingCons : ∀ {i} {id : Id} {v : Val} {st : State} {tr tr₁ : Trace₄ ∞} 
                    → st id ≡ v 
                    → tr₁ ≈ tcons st (λ where .force → tcons st (λ where .force → tr))
                    → Thunk (λ i → increasing i id (suc v) tr) i
                    → increasing i id v tr₁

            incrementingAlwaysIncrements : increasing ∞ 0 0 incrementingtrace
            incrementingAlwaysIncrements = forever _≡_.refl
                where
                    open import Relation.Binary.PropositionalEquality hiding (refl)
                    open ≡-Reasoning

                    lem₁ : {x : ℕ} → x + 1 ≡ suc x
                    lem₁ {zero} = _≡_.refl
                    lem₁ {suc x} = begin
                        suc (x + 1)
                        ≡⟨⟩
                        suc x + suc zero
                        ≡⟨ cong suc (lem₁) ⟩
                        suc (suc x)
                        ∎

                    lem₂ : ∀ {v} → (st : State) → (st 0 ≡ v) → next st 0 ≡ suc v
                    lem₂ {v} st x = begin
                        next st 0
                        ≡⟨⟩
                        st 0 + 1
                        ≡⟨ cong (_+ 1) x ⟩
                        v + 1
                        ≡⟨ lem₁ ⟩
                        suc v
                        ∎

                    forever : ∀ {i st v} → (st 0 ≡ v) → increasing i 0 v (incrementingFrom st)
                    forever {st = st} x = increasingCons x (tcons (λ { .force → tcons (λ { .force → refl }) })) λ where .force → forever (lem₂ st x)

    -- Proof of determinism of the language
    mutual
        execseqDeterministic₀ : ∀ {i} {s : Stmt} {tr₁ tr₂ tr₃ tr₄ : Trace₄ ∞} 
            → Bisim i tr₁ tr₂ 
            → execseq i s tr₁ tr₃ 
            → execseq i s tr₂ tr₄ 
            → Bisim i tr₃ tr₄
        execseqDeterministic₀ tnil (execseqNil exec₁) (execseqNil exec₂) = execDeterministic exec₁ exec₂
        execseqDeterministic₀ (tcons tr₁′≈tr₂′) (execseqCons _ _ _ exs₁) (execseqCons _ _ _ exs₂) = tcons (λ where .force → execseqDeterministic₀ (force tr₁′≈tr₂′) (force exs₁) (force exs₂))


        execDeterministic : ∀ {i} {s : Stmt} {st : State} {tr₁ tr₂ : Trace₄ ∞} 
            → exec i s st tr₁ 
            → exec i s st tr₂ 
            → Bisim i tr₁ tr₂
        execDeterministic execSkip execSkip = refl
        execDeterministic (execAssign tr₁) (execAssign tr₂) = trans tr₁ (sym tr₂)
        execDeterministic (execSeq _ _ exec₁ exs₁) (execSeq _ _ exec₂ exs₂) = execseqDeterministic₀ (execDeterministic exec₁ exec₂) exs₁ exs₂
        execDeterministic (execIfThenElseTrue _ _ exs₁) (execIfThenElseTrue _ _ exs₂) = execseqDeterministic₀ refl exs₁ exs₂
        execDeterministic (execIfThenElseTrue _ c＝true _) (execIfThenElseFalse _ c＝false _) rewrite c＝true = contradiction c＝false λ ()
        execDeterministic (execIfThenElseFalse _ c＝false _) (execIfThenElseTrue _ c＝true _) rewrite c＝true = contradiction c＝false λ ()
        execDeterministic (execIfThenElseFalse _ _ exs₁) (execIfThenElseFalse _ _ exs₂) = execseqDeterministic₀ refl exs₁ exs₂
        execDeterministic (execWhileFalse _ _ tr₁) (execWhileFalse _ _ tr₂) = trans tr₁ (sym tr₂)
        execDeterministic (execWhileFalse _ c＝false _) (execWhileLoop _ _ c＝true _ _) rewrite c＝true = contradiction c＝false λ ()
        execDeterministic (execWhileLoop _ _ c＝true _ _) (execWhileFalse _ c＝false _) rewrite c＝true = contradiction c＝false λ ()
        execDeterministic (execWhileLoop _ _ _ (execseqCons _ _ _ body₁) (execseqCons _ _ _ loop₁)) 
                          (execWhileLoop _ _ _ (execseqCons _ _ _ body₂) (execseqCons _ _ _ loop₂)) 
                          = tcons (λ where .force → execseqDeterministic₀ (execseqDeterministic₀ refl (force body₁) (force body₂)) (force loop₁) (force loop₂))


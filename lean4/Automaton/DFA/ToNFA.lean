import Automaton.DFA.Basic
import Automaton.NFA.Basic

/-!
  This file contains conversion from DFA to NFA `dfa_to_nfa`
  Proves several things about such converted automata such as equality of δ_star function
  Contains a definition of what equality between NFA and DFA means
  Then asserts that the converted DFA fulfills this property
-/

open DFA NFA

namespace ToNFA

variable {σ : Type _} (td sd : DFA σ) (tn sn : NFA σ)

-- dfa and nfa accept the same language
def dfa_nfa_eq : Prop := ∀ w : word σ , nfa_accepts tn w ↔ dfa_accepts td w

-- to convert into nfa δ, just create singleton for each state
def dfa_δ_to_nfa_δ : td.q → σ → Set td.q := λ q s => {td.δ q s}

-- conversion from nfa to dfa
def dfa_to_nfa : NFA σ := by
  exact {q := td.q , init := td.init , fs := td.fs , δ := dfa_δ_to_nfa_δ td : NFA σ}

-- the initial state in NFA is same as in the original DFA
theorem dfa_to_nfa_eq_init : td.init = (dfa_to_nfa td).init := by
  dsimp [dfa_to_nfa]

-- the final states of the converted dfa are the same
theorem dfa_to_nfa_eq_final : td.fs = (dfa_to_nfa td).fs := by dsimp[dfa_to_nfa]

-- the δ_star function remains the same (but NFA produces singletons)
theorem dfa_to_nfa_eq_δ_star  (w : word σ) : {DFA.δ_star td w} = NFA.δ_star (dfa_to_nfa td) w := by
  induction w with
  | nil => dsimp [DFA.δ_star,NFA.δ_star]; rw [←dfa_to_nfa_eq_init]
  | cons a as h => dsimp [DFA.δ_star,NFA.δ_star]; rw [←h]; simp [δ_step,dfa_to_nfa,dfa_δ_to_nfa_δ]

-- converted dfa accepts the same language as the original dfa
theorem dfa_to_nfa_eq : dfa_nfa_eq td (dfa_to_nfa td) := by
  dsimp [dfa_nfa_eq]
  intro w
  apply Iff.intro
  · intro h
    simp [nfa_accepts] at h
    simp [dfa_accepts]
    rw [←(dfa_to_nfa_eq_δ_star td w)] at h
    apply (Iff.mp Set.singleton_inter_nonempty)
    exact h
  · intro h
    simp [nfa_accepts]
    simp [dfa_accepts] at h
    rw [←(dfa_to_nfa_eq_δ_star td w)] 
    apply (Iff.mpr Set.singleton_inter_nonempty)
    exact h

end ToNFA



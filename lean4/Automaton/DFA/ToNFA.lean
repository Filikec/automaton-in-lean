import Automaton.DFA.Basic
import Automaton.NFA.Basic
import Automaton.Finset.Basic

/-!
  This file contains conversion from DFA to NFA `dfa_to_nfa`
  Proves several things about such converted automata such as equality of δ_star function
  Contains a definition of what equality between NFA and DFA means
  Then asserts that the converted DFA fulfills this property
-/

open DFA NFA

namespace ToNFA

variable {σ : Type _} [DecidableEq σ]  {q : Type _} [DecidableEq q]  (td sd : DFA σ q) (tn sn : NFA σ q)


-- to convert into nfa δ, just create singleton for each state
def dfa_δ_to_nfa_δ : td.qs → td.σs → Finset td.qs := λ q e => {td.δ q e}

-- conversion from nfa to dfa
def dfa_to_nfa : NFA σ q := by
  exact {qs := td.qs , init := td.init , fs := td.fs , δ := dfa_δ_to_nfa_δ td : NFA σ q}

-- the initial state in NFA is same as in the original DFA
theorem dfa_to_nfa_eq_init : td.init = (dfa_to_nfa td).init := by simp [dfa_to_nfa]

-- the final states of the converted dfa are the same
theorem dfa_to_nfa_eq_final : td.fs = (dfa_to_nfa td).fs := by simp [dfa_to_nfa]
-- the δ_star function remains the same (but NFA produces singletons)
theorem dfa_to_nfa_eq_δ_star' (w : word td.σs) : (q : td.qs) → {DFA.δ_star' td q w} = NFA.δ_star' (dfa_to_nfa td) {q} w := by
  induction w with
  | nil => intro q; simp [DFA.δ_star,NFA.δ_star]
  | cons a as h => intro q
                   simp [DFA.δ_star,NFA.δ_star]
                   rw [h]
                   simp [δ_step,dfa_to_nfa,dfa_δ_to_nfa_δ]

theorem dfa_to_nfa_eq_δ_star (w : word td.σs) : {DFA.δ_star td w} = NFA.δ_star (dfa_to_nfa td) w := by
  simp [DFA.δ_star, NFA.δ_star]
  have h : (dfa_to_nfa td).init = td.init := by simp [dfa_to_nfa]
  rw [h]
  apply dfa_to_nfa_eq_δ_star'

-- converted dfa accepts the same language as the original dfa
theorem dfa_to_nfa_eq : dfa_accepts td w ↔ nfa_accepts (dfa_to_nfa td) w := by
  simp only [dfa_accepts,nfa_accepts,DFA.δ_star,NFA.δ_star]
  apply Iff.intro
  · intro h
    rw [←(dfa_to_nfa_eq_δ_star' td w)]
    simp only [dfa_to_nfa]
    apply Finset.in_nonempty_inter_singleton
    exact h
  · intro h
    rw [←(dfa_to_nfa_eq_δ_star' td w)] at h
    simp only [dfa_to_nfa]
    apply Finset.nonempty_inter_singleton_imp_in
    exact h

end ToNFA

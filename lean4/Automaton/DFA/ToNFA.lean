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

variable {σ : Type _} {q : Type _}  {σs : Finset σ} {qs : Finset q} [DecidableEq σ] [DecidableEq q] (r s td : DFA σs qs)

-- conversion from nfa to dfa
def dfa_to_nfa : NFA σs qs := {q₀ := td.q₀ , fs := td.fs , δ := fun q e => {td.δ q e} }

-- the δ_star function remains the same (but NFA produces singletons)
theorem dfa_to_nfa_eq_δ_star' (w : word σs) : (q : qs) → {DFA.δ_star' td q w} = NFA.δ_star' (dfa_to_nfa td) {q} w := by
  induction w with
  | nil => intro q; simp [DFA.δ_star,NFA.δ_star]
  | cons a as h => intro q
                   simp only [DFA.δ_star,NFA.δ_star,DFA.δ_star']
                   rw [h]
                   simp [dfa_to_nfa]

theorem dfa_to_nfa_eq_δ_star (w : word σs) : {DFA.δ_star td w} = NFA.δ_star (dfa_to_nfa td) w := by
  simp only [DFA.δ_star, NFA.δ_star,dfa_to_nfa]
  apply dfa_to_nfa_eq_δ_star'

-- converted dfa accepts the same language as the original dfa
theorem dfa_to_nfa_eq : dfa_accepts td w ↔ nfa_accepts (dfa_to_nfa td) w := by
  simp only [dfa_accepts,nfa_accepts]
  rw [←dfa_to_nfa_eq_δ_star]
  apply Iff.intro
  · intro h
    apply Finset.in_nonempty_inter_singleton
    exact h
  · intro h
    apply Finset.nonempty_inter_singleton_imp_in
    exact h

end ToNFA

import Automaton.NFA.Basic
import Automaton.DFA.Basic
import Mathlib.Data.Finset.Powerset

/-!
  This file contains conversion from NFA to DFA `nfa_to_dfa`
  Proves several things about such converted automata such as equality of δ_star function
  Then asserts that the converted DFA fulfills this property
-/

open NFA DFA Finset

namespace ToDFA

variable {σ : Type _} {q : Type _} [DecidableEq σ] [DecidableEq q] (r s tn : @NFA σ q)

@[simp]
def nfa_to_dfa_q : Finset (Finset tn.qs) := tn.qs.attach.powerset

@[simp]
theorem all_in_q (q : Finset tn.qs) : q ∈ nfa_to_dfa_q tn := by
  simp [nfa_to_dfa_q,finenum_to_finset, · ⊆ ·]

@[simp]
def nfa_to_dfa_init : { x // x ∈ nfa_to_dfa_q tn } := ⟨{tn.init} , all_in_q tn {tn.init}⟩

@[simp]
def nfa_to_dfa_fs : Finset { x // x ∈ nfa_to_dfa_q tn } := by
  have fs := (nfa_to_dfa_q tn).filter (fun q => (q ∩ tn.fs).Nonempty)
  apply fs.biUnion
  intro q
  exact {⟨q , all_in_q tn q⟩}

def nfa_to_dfa_δ : { x // x ∈ nfa_to_dfa_q tn } → tn.σs → { x // x ∈ nfa_to_dfa_q tn } := by
  intro q e
  have q₁ : Finset tn.qs := q.1.biUnion (fun q => tn.δ q e)
  exact ⟨q₁ , all_in_q tn q₁⟩

def nfa_to_dfa : @DFA σ (Finset {x // x ∈ tn.qs}) :=
  {qs := nfa_to_dfa_q tn, σs := tn.σs,  init := nfa_to_dfa_init tn, fs := nfa_to_dfa_fs tn , δ := nfa_to_dfa_δ tn}

theorem δ_star_eq' : (q : Finset tn.qs) → ⟨(NFA.δ_star' tn q w) , all_in_q tn (NFA.δ_star' tn q w)⟩ = DFA.δ_star' (nfa_to_dfa tn) ⟨ q , (all_in_q tn q)⟩  w := by
  induction w with
  | nil => simp [NFA.δ_star,DFA.δ_star,nfa_to_dfa]
  | cons a as s => intro q
                   simp [NFA.δ_star,DFA.δ_star,s,nfa_to_dfa,nfa_to_dfa_δ,δ_step]

theorem δ_star_eq : ⟨(NFA.δ_star tn w) , all_in_q tn (NFA.δ_star tn w)⟩ = DFA.δ_star (nfa_to_dfa tn) w := by
  apply δ_star_eq'

theorem nfa_to_dfa_eq (w : word tn.σs) : nfa_accepts tn w ↔ dfa_accepts (nfa_to_dfa tn) w := by
  simp only [nfa_accepts,dfa_accepts]
  apply Iff.intro
  · intro a
    rw [←δ_star_eq]
    simp [nfa_to_dfa]
    apply And.intro
    · simp [finenum_to_finset,·⊆·]
    · exact a
  · intro a
    rw [←δ_star_eq] at a
    simp [nfa_to_dfa] at a
    exact a.2

end ToDFA

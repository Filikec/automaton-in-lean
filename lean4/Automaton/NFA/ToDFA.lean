import Automaton.NFA.Basic
import Automaton.DFA.Basic
import Mathlib.Data.Finset.Powerset

/-!
  This file contains conversion from NFA to DFA `nfa_to_dfa`
  Proves several things about such converted automata such as equality of δ_star function
  Then asserts that the converted DFA fulfills this property
-/

open NFA DFA

namespace ToDFA

variable {σ : Type _} [FinEnum σ] (tn : NFA σ)

@[simp]
def nfa_to_dfa_q : Finset (Finset tn.q) := by
  have qs : Finset tn.q := ⟨ Multiset.ofList (FinEnum.toList tn.q) , by apply FinEnum.nodup_toList⟩
  exact qs.powerset

@[simp]
def nfa_to_dfa_init : { x // x ∈ nfa_to_dfa_q tn } := ⟨{tn.init} , by simp [nfa_to_dfa_q]⟩ 

@[simp]
theorem all_in_q (q : Finset tn.q) : q ∈ nfa_to_dfa_q tn := by
  simp [nfa_to_dfa_q, · ⊆ ·]

@[simp]
def nfa_to_dfa_fs : Finset { x // x ∈ nfa_to_dfa_q tn } := by
  have fs := (nfa_to_dfa_q tn).filter (fun q => (q ∩ tn.fs).Nonempty)
  apply fs.biUnion
  intro q
  exact {⟨q , all_in_q tn q⟩}
  
def nfa_to_dfa_δ : { x // x ∈ nfa_to_dfa_q tn } → σ → { x // x ∈ nfa_to_dfa_q tn } := by
  intro q e
  have q₁ : Finset tn.q := q.1.biUnion (fun q => tn.δ q e)
  exact ⟨q₁ , all_in_q tn q₁⟩

def nfa_to_dfa : DFA σ := 
  {q := nfa_to_dfa_q tn, init := nfa_to_dfa_init tn, fs := nfa_to_dfa_fs tn , δ := nfa_to_dfa_δ tn} 


theorem δ_star_eq' : (q : Finset tn.q) → ⟨(NFA.δ_star' tn q w) , all_in_q tn (NFA.δ_star' tn q w)⟩ = (DFA.δ_star' (nfa_to_dfa tn) ⟨ q , (all_in_q tn q)⟩  w) := by
  induction w with
  | nil => simp [NFA.δ_star,DFA.δ_star,nfa_to_dfa]
  | cons a as s => intro q
                   simp [NFA.δ_star,DFA.δ_star]
                   rw [s]
                   simp [nfa_to_dfa,nfa_to_dfa_δ,δ_step]

theorem δ_star_eq : ⟨(NFA.δ_star tn w) , all_in_q tn (NFA.δ_star tn w)⟩ = (DFA.δ_star (nfa_to_dfa tn) w) := by
  simp [NFA.δ_star,DFA.δ_star]
  apply δ_star_eq'


theorem nfa_to_dfa_eq (w : word σ) : nfa_accepts tn w ↔ dfa_accepts (nfa_to_dfa tn) w := by
  have h : (nfa_to_dfa tn).init = ⟨{tn.init} , all_in_q tn {tn.init}⟩ := by simp [nfa_to_dfa]
  apply Iff.intro
  · dsimp [nfa_accepts,dfa_accepts]
    intro a
    rw [h,←δ_star_eq']
    simp [nfa_to_dfa]
    apply And.intro
    · simp [·⊆·]
    · exact a
  · simp [nfa_accepts,dfa_accepts]
    intro a
    rw [h,←δ_star_eq'] at a
    simp [nfa_to_dfa] at a
    exact a.2
    
end ToDFA
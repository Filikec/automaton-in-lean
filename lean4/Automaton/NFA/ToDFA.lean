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

variable {σ : Type _} {q : Type _} {σs : Finset σ} {qs : Finset q} (r s tn : NFA σs qs) [DecidableEq σ] [DecidableEq q]

@[simp]
def nfa_to_dfa_q : Finset (Finset qs) := qs.attach.powerset

@[simp]
theorem all_in_q (q : Finset qs) : q ∈ nfa_to_dfa_q  := by
  simp [nfa_to_dfa_q, · ⊆ ·]

@[simp]
def nfa_to_dfa_init : { x // x ∈ @nfa_to_dfa_q q qs } := ⟨tn.q₀ , all_in_q tn.q₀⟩

@[simp]
def nfa_to_dfa_fs : Finset { x // x ∈ @nfa_to_dfa_q q qs } :=
  (nfa_to_dfa_q.filter (fun q => (q ∩ tn.fs).Nonempty)).map  ⟨(fun q => ⟨q , all_in_q  q⟩), by simp [Function.Injective]⟩


def nfa_to_dfa_δ : { x // x ∈ @nfa_to_dfa_q q qs } → σs → { x // x ∈ @nfa_to_dfa_q q qs } := by
  intro q e
  exact ⟨q.1.biUnion (fun q => tn.δ q e) , all_in_q _⟩

def nfa_to_dfa : DFA σs (@nfa_to_dfa_q q qs) :=
  {q₀ := nfa_to_dfa_init tn, fs := nfa_to_dfa_fs tn , δ := nfa_to_dfa_δ tn}

theorem δ_star_eq' : (q : Finset qs) → ⟨(NFA.δ_star' tn q w) , all_in_q  (NFA.δ_star' tn q w)⟩ = DFA.δ_star' (nfa_to_dfa tn) ⟨ q , (all_in_q q)⟩  w := by
  induction w with
  | nil => simp [NFA.δ_star,DFA.δ_star,nfa_to_dfa]
  | cons a as s => intro q
                   simp [NFA.δ_star,DFA.δ_star,s,nfa_to_dfa,nfa_to_dfa_δ,δ_step]

theorem δ_star_eq : ⟨(NFA.δ_star tn w) , all_in_q (NFA.δ_star tn w)⟩ = DFA.δ_star (nfa_to_dfa tn) w := by
  apply δ_star_eq'

theorem nfa_to_dfa_eq (w : word σs) : nfa_accepts tn w ↔ dfa_accepts (nfa_to_dfa tn) w := by
  simp only [nfa_accepts,dfa_accepts]
  apply Iff.intro
  · intro a
    rw [←δ_star_eq]
    simp [nfa_to_dfa]
    apply And.intro
    · simp [·⊆·]
    · exact a
  · intro a
    rw [←δ_star_eq] at a
    simp [nfa_to_dfa] at a
    exact a.2

instance instDecidableExWNeNil : Decidable (∃ a, a ∈ nfaLang tn ∧ a ≠ []) := by
  have : Decidable (∃ w, DFA.dfa_accepts (nfa_to_dfa tn) w ∧ w ≠ []) := by infer_instance
  match this with
  | isTrue h => apply Decidable.isTrue
                simp only [nfaLang]
                apply Exists.elim h
                intro w h
                rw [←nfa_to_dfa_eq] at h
                exists w
  | isFalse h => apply Decidable.isFalse
                 intro ex
                 simp only [nfaLang] at ex
                 apply Exists.elim ex
                 intro w hin
                 apply h
                 exists w
                 rw [←nfa_to_dfa_eq]
                 apply hin

end ToDFA

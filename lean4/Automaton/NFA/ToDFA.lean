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

variable {σ : Type _} {q : Type _} {q₁ : Type _}  {σs : Finset σ} (tn : NFA σs q) [DecidableEq σ] [DecidableEq q] [DecidableEq q₁]  (r : NFA σs q₁)

@[simp]
def nfa_to_dfa_q : Finset (Finset tn.qs) := tn.qs.attach.powerset

@[simp]
theorem all_in_q (q : Finset tn.qs) : q ∈ nfa_to_dfa_q tn := by
  simp [nfa_to_dfa_q, · ⊆ ·]

@[simp]
def nfa_to_dfa_init : { x // x ∈ nfa_to_dfa_q tn } := ⟨tn.q₀ , all_in_q _ tn.q₀⟩

@[simp]
def nfa_to_dfa_fs : Finset { x // x ∈ nfa_to_dfa_q tn } :=
  ((nfa_to_dfa_q tn).filter (fun q => (q ∩ tn.fs).Nonempty)).map  ⟨(fun q => ⟨q , all_in_q tn q⟩), by simp [Function.Injective]⟩


def nfa_to_dfa_δ : { x // x ∈ nfa_to_dfa_q tn } → σs → { x // x ∈ nfa_to_dfa_q tn } := by
  intro q e
  exact ⟨q.1.biUnion (fun q => tn.δ q e) , all_in_q tn _⟩

def nfa_to_dfa : DFA σs (Finset tn.qs) :=
  {q₀ := nfa_to_dfa_init tn, fs := nfa_to_dfa_fs tn , δ := nfa_to_dfa_δ tn}


theorem δ_star_eq' : (q : Finset tn.qs) → ⟨(NFA.δ_star' tn q w) , all_in_q tn _⟩ = DFA.δ_star' (nfa_to_dfa tn) ⟨q , (all_in_q tn q)⟩  w := by
  induction w with
  | nil => simp [NFA.δ_star,DFA.δ_star,nfa_to_dfa]
  | cons a as s => intro q
                   simp [NFA.δ_star,DFA.δ_star,s,nfa_to_dfa,nfa_to_dfa_δ,δ_step]

theorem δ_star_eq : ⟨(NFA.δ_star tn w) , all_in_q tn (NFA.δ_star  tn w)⟩ = DFA.δ_star (nfa_to_dfa tn) w := by
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

instance decExPrefix : Decidable (∃ a b, nfa_accepts tn a ∧ a ++ b = w) := by
  have h : Decidable (∃ a b, DFA.dfa_accepts (nfa_to_dfa tn) a ∧ a ++ b = w) := by infer_instance
  match h with
  | isTrue h => apply isTrue
                apply Exists.elim h
                intro a ex
                apply Exists.elim ex
                intro b h
                rw [←nfa_to_dfa_eq] at h
                exists a
                exists b
  | isFalse h => apply isFalse
                 intro h'
                 apply h
                 apply Exists.elim h'
                 intro a ex
                 apply Exists.elim ex
                 intro b h
                 rw [nfa_to_dfa_eq] at h
                 exists a
                 exists b

instance decExSplit  : Decidable (∃ a b, nfa_accepts r a ∧ nfa_accepts tn b ∧ a ++ b = w) := by
  have f : Fintype {p : List σs // p.length <= w.length} := by infer_instance
  have h : Decidable (∃ a, a ∈ f.elems ∧ (fun a => nfa_accepts r a ∧ ∃ b, b ∈ f.elems ∧ nfa_accepts tn b ∧ a++b = w) a) := Finset.decidableExistsAndFinset
  match h with
  | isTrue t => apply isTrue
                apply Exists.elim t
                intro l la
                exists l
                apply Exists.elim la.2.2
                intro lb h
                exists lb
                exact ⟨la.2.1,h.2.1,h.2.2⟩
  | isFalse g => apply isFalse
                 intro ex
                 apply g
                 apply Exists.elim ex
                 intro a ex
                 apply Exists.elim ex
                 intro b h
                 have t₁ := List.length_append a b
                 have t₂ : List.length a + List.length b = List.length w := by rw [←t₁,←h.2.2]
                 have h₁ : List.length a <= List.length w := by rw [←t₂]; simp
                 have h₂ : List.length b <= List.length w := by rw [←t₂]; simp
                 exists ⟨a,h₁⟩
                 apply And.intro
                 · apply Fintype.complete
                 · simp only []
                   apply And.intro
                   · exact h.1
                   · exists ⟨b,h₂⟩
                     exact ⟨Fintype.complete _,h.2.1,h.2.2⟩


end ToDFA

import Automaton.DFA.Basic
import Automaton.Finset.Basic
import Mathlib.Data.FinEnum
import Mathlib.Data.List.Basic

open DFA Finset

namespace DFA

variable {σ : Type _} {q : Type _} (r s t : DFA σ q) [DecidableEq σ] [DecidableEq q]

@[simp]
def minimization_reachable_q : Finset t.qs := t.qs.attach.filter (fun q => reachable t t.init q)

@[simp]
def minimization_reachable_init : { x // x ∈ minimization_reachable_q t } := by
  exact ⟨t.init , by simp [finenum_to_finset]; exact reachable.base⟩

@[simp]
def minimization_reachable_fs : Finset {x // x ∈ minimization_reachable_q t} := by
  have := Finset.attach (minimization_reachable_q t)
  exact this.filter (fun q => q.1 ∈ t.fs)

@[simp]
def minimization_reachable_δ : { x // x ∈ minimization_reachable_q t } → t.σs → { x // x ∈ minimization_reachable_q t } := by
  intro q e
  have := q.2
  simp [finenum_to_finset] at this
  exact ⟨ t.δ q e, by simp [finenum_to_finset]; apply reachable.step; exact this⟩

def minimization_reachable : DFA σ {x // x ∈ t.qs} :=
  {qs := minimization_reachable_q t, init := minimization_reachable_init t, fs := minimization_reachable_fs t, δ := minimization_reachable_δ t}

lemma minimization_reachable_δ_star'_eq (w : word t.σs) : (q : t.qs) → (r : reachable t t.init q) → δ_star' t q w = (δ_star' (minimization_reachable t) ⟨q, by simp [finenum_to_finset, minimization_reachable]; exact r⟩  w).1 := by
  induction w with
  | nil => simp
  | cons a as s => simp only [δ_star']
                   intro q r
                   rw [s]
                   simp [minimization_reachable]
                   apply reachable.step
                   exact r

theorem minimization_reachable_δ_star_eq (w : word t.σs) : δ_star t w = (δ_star (minimization_reachable t) w).1 := by
  simp only [δ_star]
  apply minimization_reachable_δ_star'_eq
  exact reachable.base

theorem minimization_reachable_eq (w : word t.σs) : dfa_accepts t w ↔ dfa_accepts (minimization_reachable t) w := by
  apply Iff.intro
  · intro dfa
    simp only [dfa_accepts] at dfa
    simp only [dfa_accepts]
    simp [minimization_reachable]
    rw [minimization_reachable_δ_star_eq] at dfa
    simp [minimization_reachable] at dfa
    exact dfa
  · intro dfa
    simp only [dfa_accepts] at dfa
    simp only [dfa_accepts]
    rw [minimization_reachable_δ_star_eq]
    simp [minimization_reachable] at dfa
    simp [minimization_reachable]
    exact dfa

-- all states reachable from current state
inductive distinct : t.qs → t.qs → Prop where
  | base (a b : t.qs) : (a ∈ t.fs ∧ b ∉ t.fs) ∨ (a ∉ t.fs ∧ b ∈ t.fs) → distinct a b
  | step (a b : t.qs) : ∀ s : t.σs, distinct (t.δ a s) (t.δ b s) → distinct a b

def nondistinct (a b : t.qs) : Prop := ¬ distinct t a b

lemma distinct_if_not_iff_in_fs {a b : t.qs} : ¬(a ∈ t.fs ↔ b ∈ t.fs) → distinct t a b := by
  intro iff
  simp only [δ_star']
  have h₁ := Decidable.not_iff.mp iff
  have h₂ := Decidable.not_iff_comm.mp h₁
  apply distinct.base
  cases (Decidable.em (a ∈ t.fs)) with
  | inl l => apply Or.inl
             apply And.intro
             · exact l
             · apply h₂.2
               exact l
  | inr r => apply Or.inr
             exact ⟨r , h₁.mp r⟩


lemma distinct_if_δ_star'_distinct (w : word t.σs) : (a b : t.qs) → distinct t (δ_star' t a w) (δ_star' t b w) → distinct t a b := by
  induction w using List.reverseRecOn  with
  | H0 => intro a b d
          simp at d
          exact d
  | H1 a b s => intro a b d
                rw [←δ_δ_star'_concat_eq_δ_star',←δ_δ_star'_concat_eq_δ_star'] at d
                apply s
                apply distinct.step
                exact d

theorem distinct_iff_ex_notaccepted (a b : t.qs) : distinct t a b ↔ (∃ w : word t.σs, ¬ ((δ_star' t a w) ∈ t.fs ↔ (δ_star' t b w) ∈ t.fs)) := by
  apply Iff.intro
  · intro d
    induction d with
    | base c d s => exists []
                    simp only [δ_star']
                    intro iff
                    cases s with
                    | inl l => apply l.2
                               apply iff.mp
                               exact l.1
                    | inr r => apply r.1
                               apply iff.mpr
                               exact r.2
    | step c d s _ h => apply Exists.elim h
                        intro w iff
                        exists (s :: w)
  · intro ex
    apply Exists.elim ex
    intro w niff
    induction w using List.reverseRecOn with
    | H0 => simp at niff
            apply distinct_if_not_iff_in_fs
            exact niff
    | H1 => rw [←δ_δ_star'_concat_eq_δ_star',←δ_δ_star'_concat_eq_δ_star'] at niff
            have := distinct_if_not_iff_in_fs t niff
            apply distinct_if_δ_star'_distinct
            apply distinct.step
            exact this


lemma distinct_if_word (w : word t.σs) : (a b : t.qs) → (δ_star' t a w ∉ t.fs ↔ δ_star' t b w ∈ t.fs) → distinct t a b := by
  induction w using List.reverseRecOn  with
  | H0 => intro a b ex
          simp at ex
          apply distinct.base
          have := Decidable.iff_iff_and_or_not_and_not.mp ex
          apply Or.symm
          rw [Decidable.not_not] at this
          exact this
  | H1 es e _ => intro a b ex
                 rw [←δ_δ_star'_concat_eq_δ_star',←δ_δ_star'_concat_eq_δ_star'] at ex
                 have := distinct_if_not_iff_in_fs t (Decidable.not_iff.mpr ex)
                 have : distinct t (δ_star' t a es) (δ_star' t b es) := by apply distinct.step
                                                                           exact this

                 apply distinct_if_δ_star'_distinct
                 exact this

theorem distinct_iff_ex_word (a b : t.qs) : (∃ l : word t.σs, δ_star' t a l ∉ t.fs ↔ δ_star' t b l ∈ t.fs) ↔ distinct t a b := by
  apply Iff.intro
  · intro ex
    apply Exists.elim ex
    intro a ex
    apply distinct_if_word
    · exact ex
  · intro d
    induction d with
    | base a b h => exists []
                    simp only [δ_star']
                    apply Decidable.iff_iff_and_or_not_and_not.mpr
                    apply Or.symm
                    rw [Decidable.not_not]
                    exact h
    | step a b g _ s => apply Exists.elim s
                        intro c ex
                        exists (g::c)

lemma nondistinct_iff_nex_notaccepted : nondistinct t a b ↔ (¬∃ w : word t.σs, ¬((δ_star' t a w) ∈ t.fs ↔ (δ_star' t b w) ∈ t.fs)) := by
  simp only [nondistinct]
  apply not_congr
  apply distinct_iff_ex_notaccepted



theorem nondistinct_iff_forall_accepted : nondistinct t a b ↔ (∀ w : word t.σs, ((δ_star' t a w) ∈ t.fs ↔ (δ_star' t b w) ∈ t.fs)) := by
  rw [←Decidable.not_exists_not]
  apply nondistinct_iff_nex_notaccepted

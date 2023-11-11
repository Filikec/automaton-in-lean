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

inductive distinct : t.qs → t.qs → Prop where
  | base (a b : t.qs) : ¬(a ∈ t.fs ↔ b ∈ t.fs) → distinct a b
  | step (a b : t.qs) : ∀ s : t.σs, distinct (t.δ a s) (t.δ b s) → distinct a b

def nondistinct (a b : t.qs) : Prop := ¬ distinct t a b

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

theorem distinct_iff_ex_notaccepted (a b : t.qs) : distinct t a b ↔ ∃ l : word t.σs, ¬(δ_star' t a l ∈ t.fs ↔ δ_star' t b l ∈ t.fs) := by
  apply Iff.intro
  · intro d
    induction d with
    | base a b h => exists []
    | step a b g _ s => apply Exists.elim s
                        intro c ex
                        exists (g::c)
  · intro ex
    apply Exists.elim ex
    intro c ex
    have : distinct t (δ_star' t a c) (δ_star' t b c) := by apply distinct.base
                                                            exact ex
    apply distinct_if_δ_star'_distinct
    exact this

lemma nondistinct_iff_nex_notaccepted : nondistinct t a b ↔ ¬∃ w : word t.σs, ¬(δ_star' t a w ∈ t.fs ↔ δ_star' t b w ∈ t.fs) := by
  simp only [nondistinct]
  apply not_congr
  apply distinct_iff_ex_notaccepted

theorem nondistinct_iff_forall_accepted : nondistinct t a b ↔ ∀ w : word t.σs, (δ_star' t a w ∈ t.fs ↔ δ_star' t b w ∈ t.fs) := by
  rw [←Decidable.not_exists_not]
  apply nondistinct_iff_nex_notaccepted


def get_all_pairs : Finset (t.qs × t.qs) := t.qs.attach.biUnion (fun q₁ => t.qs.attach.biUnion (fun q₂ => {⟨q₁,q₂⟩}))

def start : Finset (t.qs × t.qs) := (get_all_pairs t).filter (fun (a,b) => ¬(a ∈ t.fs ↔ b ∈ t.fs))

def step (c a : Finset (t.qs × t.qs)) : Finset (t.qs × t.qs) :=  c ∪ (a.filter (fun (a,b) => ∃ s : t.σs, (t.δ a s, t.δ b s) ∈ c))

lemma card_ne_ne {fa fb : Finset α} : fa.card ≠ fb.card → fa ≠ fb := by
  intro ne
  intro eq
  apply ne
  rw [eq]

def aux (c : Finset (t.qs × t.qs)) (h : c ⊆ (get_all_pairs t)) : Finset (t.qs × t.qs) := by
  let a := get_all_pairs t
  if g : (step t c a).card = c.card then exact c else have h₁ : (step t c a).card >= c.card := by simp only [step]
                                                                                                  apply Finset.card_le_of_subset
                                                                                                  apply Finset.subset_union_left
                                                      have h₂ : card c < card (step t c a) := by apply Nat.lt_iff_le_and_ne.mpr
                                                                                                 apply And.intro
                                                                                                 · exact h₁
                                                                                                 · simp at g
                                                                                                   intro eq
                                                                                                   apply g
                                                                                                   simp at eq
                                                                                                   apply Eq.symm
                                                                                                   exact eq
                                                      have s : step t c a ⊆ a := by simp [step]
                                                                                    apply Finset.union_subset
                                                                                    · exact h
                                                                                    · apply Finset.filter_subset
                                                      have d : c ⊂ step t c a := by apply Finset.ssubset_iff_subset_ne.mpr
                                                                                    apply And.intro
                                                                                    · simp [step]
                                                                                      apply Finset.subset_union_left
                                                                                    · apply card_ne_ne
                                                                                      apply Nat.ne_of_lt
                                                                                      exact h₂
                                                      have : a.card - (step t c a).card < a.card - c.card := by apply Nat.sub_lt_sub_left
                                                                                                                · apply Nat.lt_iff_le_and_ne.mpr
                                                                                                                  apply And.intro
                                                                                                                  · apply Finset.card_le_of_subset
                                                                                                                    exact h
                                                                                                                  · apply Nat.ne_of_lt
                                                                                                                    apply Finset.card_lt_card
                                                                                                                    apply Finset.ssubset_of_ssubset_of_subset
                                                                                                                    · exact d
                                                                                                                    · exact s
                                                                                                                · exact h₂
                                                      exact aux (step t c a) s

termination_by aux c h => (get_all_pairs t).card - c.card

lemma start_subset_all : (start t) ⊆ (get_all_pairs t) := by
  simp [start]

def table_filling : Finset (t.qs × t.qs) := aux t (start t) (start_subset_all t)

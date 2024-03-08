import Mathlib.Data.Set.Lattice
import Automaton.Language.Basic
import Automaton.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.FinEnum
import Automaton.Regex.Basic

/-!
  This file contains the definition of NFA as well as a few fundemantal operations
  * `δ_star` and `accepts` functions
-/

namespace NFA

structure NFA (σs : Finset σ) where
  q : Type _
  qs : Finset q
  q₀ : Finset qs          -- initial state
  fs : Finset qs          -- accepting states
  δ : qs → σs → Finset qs -- transition function
  [d₁ : DecidableEq q]
  [d₂ : DecidableEq σ]


variable {σ : Type _} {q : Type _} {σs : Finset σ} (t : NFA σs) [DecidableEq σ] [DecidableEq q]

instance decEqQ : DecidableEq t.q := t.d₁
instance decEqσ : DecidableEq σ := t.d₂

-- one step in the operation of NFA, consuming one character
-- take the union of all sets of states reachable from current set of states
@[simp]
def δ_step  (q : Finset t.qs) (e : σs) : Finset t.qs := q.biUnion (fun n => t.δ n e)

-- δ* function for NFA
-- returns set of states reached after inputting a word
@[simp]
def δ_star' (q : Finset t.qs) : (w : word σs) → Finset t.qs
  | [] => q
  | e :: es => δ_star' (δ_step t q e) es

@[simp]
def δ_star : (w : word σs) → Finset t.qs := δ_star' t t.q₀

-- Whether a word is in the language that the NFA accepts
@[simp]
def nfa_accepts (w : word σs) : Prop := by
  have inter : Finset t.qs := (δ_star t w) ∩ t.fs
  exact inter.Nonempty

-- nfa accepts nil iff s is final
theorem nfa_accepts_nil_iff_final : nfa_accepts t [] ↔ Finset.Nonempty (t.q₀ ∩ t.fs) := by
  apply Iff.intro
  · intro ne
    simp only [nfa_accepts, δ_star,δ_star'] at ne
    exact ne
  · intro e
    simp only [nfa_accepts,δ_star]
    exact e

instance decidableAccepts (w : word σs) : Decidable (nfa_accepts t w) := by
  dsimp [nfa_accepts]
  apply Finset.decidableNonempty

def nfaLang : Lang σs := fun w => nfa_accepts t w

instance decidableLang (w : word σs) : Decidable (w ∈ nfaLang t) := by
  dsimp [nfa_accepts]
  apply Finset.decidableNonempty


lemma δ_star'_append_eq : (q : Finset t.qs) → δ_star' t (δ_star' t q l) r = δ_star' t q (l ++ r) := by
  induction l with
  | nil => simp
  | cons e es s => intro q
                   simp only [δ_star',List.append_eq]
                   apply s


theorem δ_star'_union : (a b : Finset t.qs) → δ_star' t (a ∪ b) w = δ_star' t a w ∪ δ_star' t b w := by
  induction w with
  | nil => simp
  | cons e es s => intro a b
                   simp only [δ_star',δ_step]
                   rw [Finset.biUnion_union]
                   apply s

theorem δ_subset_δ_step {q : Finset t.qs} (h : a ∈ q) : t.δ a e ⊆ δ_step t q e := by
  simp [δ_step]
  apply Finset.subset_biUnion_of_mem (fun n => NFA.δ t n e)
  exact h

theorem δ_star'_empty : δ_star' t ∅ w = ∅ := by
  induction w with
  | nil => simp
  | cons e es s => simp; assumption



end NFA

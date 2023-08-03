import Mathlib.Data.Set.Lattice
import Automaton.Language.Basic
import Automaton.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.FinEnum

/-!
  This file contains the definition of NFA as well as a few fundemantal operations
  * `δ_star` and `accepts` functions
-/

namespace NFA

structure NFA (σ : Type _) where
  q : Type _             -- states
  init : q               -- initial state
  fs : Finset q          -- accepting states
  δ : q → σ → Finset q   -- transition function
  [fq : FinEnum q]
  [fσ : FinEnum σ]

variable {σ : Type _} (t : NFA σ)

instance : FinEnum t.q := t.fq

-- one step in the operation of NFA, consuming one character
-- take the union of all sets of states reachable from current set of states
@[simp]
def δ_step  (q : Finset t.q) (e : σ) : Finset t.q := q.biUnion (fun n => t.δ n e)

-- δ* function for NFA
-- returns set of states reached after inputting a word
@[simp]
def δ_star' (q : Finset t.q) : (w : word σ) → Finset t.q
  | [] => q
  | e :: es => δ_star' (δ_step t q e) es

@[simp]
def δ_star : (w : word σ) → Finset t.q := δ_star' t {t.init}

-- Whether a word is in the language that the NFA accepts
@[simp]
def nfa_accepts (w : word σ) : Prop := by
  have inter : Finset t.q := (δ_star t w) ∩ t.fs
  exact inter.Nonempty

-- nfa accepts nil iff init is final
theorem nfa_accepts_nil_iff_final : nfa_accepts t [] ↔ t.init ∈ t.fs := by
  apply Iff.intro
  · intro ne
    dsimp [nfa_accepts, δ_star ] at ne
    apply Finset.nonempty_inter_singleton_imp_in
    exact ne
  · intro e
    dsimp [nfa_accepts,δ_star]
    rw [Finset.singleton_inter_of_mem e]
    exact (Finset.singleton_nonempty t.init)

instance decidableLang (w : word σ) : Decidable (nfa_accepts t w) := by
  dsimp [nfa_accepts]
  apply Finset.decidableNonempty

end NFA
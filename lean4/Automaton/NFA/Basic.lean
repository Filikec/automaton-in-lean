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
  [fn : FinEnum q]

variable {α : Type _}{σ : Type _} [DecidableEq α] (t : NFA σ)

instance : FinEnum t.q := t.fn

-- one step in the operation of NFA, consuming one character
-- take the union of all sets of states reachable from current set of states
def δ_step  (q : Finset t.q) (e : σ) : Finset t.q := q.biUnion (fun n => t.δ n e)

-- δ* function for NFA
-- returns set of states reached after inputting a word
def δ_star : (w : word σ) → Finset t.q
  | [] => {t.init}
  | e :: es => δ_step t (δ_star es) e 

-- Whether a word is in the language that the NFA accepts
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


end NFA
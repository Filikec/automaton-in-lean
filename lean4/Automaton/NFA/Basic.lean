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

structure NFA (σs : Finset σ) (qs : Finset q) where
  q₀ : qs                  -- initial state
  fs : Finset qs          -- accepting states
  δ : qs → σs → Finset qs -- transition function


variable {σ : Type _} {q : Type _} {σs : Finset σ} {qs : Finset q} (r s t : NFA σs qs) [DecidableEq σ] [DecidableEq q]


-- one step in the operation of NFA, consuming one character
-- take the union of all sets of states reachable from current set of states
@[simp]
def δ_step  (q : Finset qs) (e : σs) : Finset qs := q.biUnion (fun n => t.δ n e)

-- δ* function for NFA
-- returns set of states reached after inputting a word
@[simp]
def δ_star' (q : Finset qs) : (w : word σs) → Finset qs
  | [] => q
  | e :: es => δ_star' (δ_step t q e) es

@[simp]
def δ_star : (w : word σs) → Finset qs := δ_star' t {t.q₀}

-- Whether a word is in the language that the NFA accepts
@[simp]
def nfa_accepts (w : word σs) : Prop := by
  have inter : Finset qs := (δ_star t w) ∩ t.fs
  exact inter.Nonempty

-- nfa accepts nil iff s is final
theorem nfa_accepts_nil_iff_final : nfa_accepts t [] ↔ t.q₀ ∈ t.fs := by
  apply Iff.intro
  · intro ne
    simp only [nfa_accepts, δ_star ] at ne
    apply Finset.nonempty_inter_singleton_imp_in
    exact ne
  · intro e
    dsimp [nfa_accepts,δ_star]
    rw [Finset.singleton_inter_of_mem e]
    exact (Finset.singleton_nonempty t.q₀)

instance decidableLang (w : word σs) : Decidable (nfa_accepts t w) := by
  dsimp [nfa_accepts]
  apply Finset.decidableNonempty

end NFA

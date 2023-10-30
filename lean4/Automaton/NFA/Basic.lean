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

structure NFA (σ : Type _) (q : Type _) where
  σs : Finset σ    -- alphabet
  qs : Finset q    -- states
  init : qs        -- initial state
  fs : Finset qs   -- accepting states
  δ : qs → σs → Finset qs -- transition function
  [dq : DecidableEq q]
  [dσ : DecidableEq σ]

variable {σ : Type _} {q : Type _}  (r s t : NFA σ q) [DecidableEq σ] [DecidableEq q]

instance : DecidableEq t.σs := by infer_instance
instance : DecidableEq t.qs := by infer_instance

-- one step in the operation of NFA, consuming one character
-- take the union of all sets of states reachable from current set of states
@[simp]
def δ_step  (q : Finset t.qs) (e : t.σs) : Finset t.qs := q.biUnion (fun n => t.δ n e)

-- δ* function for NFA
-- returns set of states reached after inputting a word
@[simp]
def δ_star' (q : Finset t.qs) : (w : word t.σs) → Finset t.qs
  | [] => q
  | e :: es => δ_star' (δ_step t q e) es

@[simp]
def δ_star : (w : word t.σs) → Finset t.qs := δ_star' t {t.init}

-- Whether a word is in the language that the NFA accepts
@[simp]
def nfa_accepts (w : word t.σs) : Prop := by
  have inter : Finset t.qs := (δ_star t w) ∩ t.fs
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

instance decidableLang (w : word t.σs) : Decidable (nfa_accepts t w) := by
  dsimp [nfa_accepts]
  apply Finset.decidableNonempty

end NFA

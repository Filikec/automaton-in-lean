import Mathlib.Data.Set.Lattice
import Automaton.Language.Basic

/-!
  This file contains the definition of NFA as well as a few fundemantal operations
  * `δ_star` and `accepts` functions
-/

namespace NFA

structure NFA (σ : Type _) where
  q : Type _        -- states
  init : q          -- initial state
  fs : Set q        -- accepting states
  δ : q → σ → Set q -- transition function
  [d : DecidablePred fs]

variable {σ : Type _} (t : NFA σ)

-- one step in the operation of NFA, consuming one character
-- take the union of all sets of states reachable from current set of states
def δ_step  (q : Set t.q) (e : σ) : Set t.q := ⋃₀ {t.δ a e | a ∈ q}

-- δ* function for NFA
-- returns set of states reached after inputting a word
def δ_star : (w : word σ) → Set t.q 
  | [] => {t.init}
  | e :: es => δ_step t (δ_star es) e 

-- Whether a word is in the language that the NFA accepts
def nfa_accepts (w : word σ) : Prop := by
  have δ_fs : Set t.q := δ_star t w
  have i := Set.inter δ_fs t.fs 
  exact i.Nonempty

-- nfa accepts nil iff init is final
theorem nfa_accepts_nil_iff_final : nfa_accepts t [] ↔ t.init ∈ t.fs := by
  apply Iff.intro
  · intro h
    dsimp [nfa_accepts, δ_star ] at h
    apply (Iff.mp Set.singleton_inter_nonempty)
    exact h
  · intro e
    dsimp [nfa_accepts]
    apply (Iff.mpr Set.singleton_inter_nonempty)
    exact e
    
end NFA
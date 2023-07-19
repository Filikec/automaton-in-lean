import Mathlib.Data.Set.Lattice
import Automaton.Language.Basic

/-!
  This file contains the definition of NFA as well as a few fundemantal operations
  * `δ_star` and `accepts` functions
-/

namespace NFA

structure NFA where
  q : Type _        -- states
  init : q          -- initial state
  fs : Set q        -- accepting states
  σ : Type _        -- alphabet
  δ : q → σ → Set q -- transition function
  [d : DecidablePred fs]

variable (t : NFA)

-- one step in the operation of NFA, consuming one character
-- take the union of all sets of states reachable from current set of states
def δ_step (e : t.σ) (q : Set t.q) : Set t.q := ⋃₀ {t.δ a e | a ∈ q}

-- δ* function for NFA
-- returns set of states reached after inputting a word
def δ_star (q : Set t.q) : (w : word t.σ) → Set t.q 
  | [] => q
  | e :: es => δ_star (δ_step t e q) es

-- Whether a word is in the language that the NFA accepts
def accepts (w : word t.σ) : Prop := by
  have δ_fs : Set t.q := δ_star t { t.init } w
  have i := Set.inter δ_fs t.fs 
  exact i.Nonempty


end NFA
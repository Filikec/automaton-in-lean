import Automaton.NFA.Basic
import Automaton.DFA.Basic
import Mathlib.Data.Finset.Powerset

open NFA DFA

namespace ToDFA

variable {α : Type _}{σ : Type _} [DecidableEq α] (tn : NFA α σ)

-- turn nfa function into dfa
def nfa_δ_to_dfa_δ : Finset α → σ → Finset α := by
  intro q e
  exact q.biUnion (fun n => tn.δ n e)

-- δ_star for converted dfa
def δ_star (w : word σ) : Finset (Finset α) := by
  induction w with
  | nil => exact {{tn.init}}
  | cons e _ s => exact s.biUnion (fun n => {(nfa_δ_to_dfa_δ tn) n e})

-- the final state are all sets of states that include at least one final state
def fs : Finset (Finset α) := by
  exact (Finset.powerset tn.q).filter (fun q => (q ∩ tn.fs).Nonempty) 

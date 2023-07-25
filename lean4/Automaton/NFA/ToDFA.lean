import Automaton.NFA.Basic
import Automaton.DFA.Basic
import Mathlib.Data.Finset.Powerset

open NFA DFA

namespace ToDFA

variable {σ : Type _} (tn : NFA σ) (td : DFA σ )

-- turn nfa function into dfa
def nfa_δ_to_dfa_δ : Finset Nat → σ → Finset Nat := by
  intro q e
  exact q.biUnion (fun n => tn.δ n e)

-- δ_star for converted dfa
def δ_star (w : word σ) : Finset (Finset Nat) := by
  induction w with
  | nil => exact {{tn.init}}
  | cons e _ s => exact s.biUnion (fun n => {(nfa_δ_to_dfa_δ tn) n e})

-- the final state are all sets of states that include at least one final state
def fs : Finset (Finset Nat) := by
  exact (Finset.powerset tn.q).filter (fun q => (q ∩ tn.fs).Nonempty) 


end ToDFA
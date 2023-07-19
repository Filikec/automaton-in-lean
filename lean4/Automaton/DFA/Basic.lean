import Automaton.Language.Basic

/-!
  This file contains the definition of a DFA as well as a few fundamental operations it can do
  * `δ_star` and `accepts` functions.
  
  * Also asserts the decidability of the language of DFA
-/

namespace DFA

structure DFA where
  q : Type _    -- states
  init : q      -- initial state
  fs : Set q    -- accepting states
  σ : Type _    -- alphabet
  δ : q → σ → q -- transition function
  [d : DecidablePred fs]

variable (t : DFA)

-- δ* function
-- the state reached after following all transitions given a word
-- args : dfa , word , initial state 
-- (could be defined without init but words would then be reversed as written, see Examples)
def δ_star : (w : word t.σ) → (initState : t.q) → t.q
  | [] , cur => cur
  | e :: es , cur => δ_star es (t.δ cur e)

-- whether a DFA accepts a word
def accepts : (w : word t.σ) → Prop := by
  intro w
  have f := δ_star t w t.init
  apply f ∈ t.fs

def dfaLang : Lang t.σ := fun w => accepts t w

-- DFA language is decidable
instance decidableLang (w : word t.σ) [d : DecidablePred (t.fs)] : Decidable (accepts t w) := by
  dsimp [accepts]
  generalize δ_star t w = e
  apply d

-- the set predicate is decidable
instance decDFA : DecidablePred (t.fs) := by
  exact t.d
  

end DFA
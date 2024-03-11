import Mathlib.Data.Finset.Sum
import Mathlib.Logic.Embedding.Basic
import Automaton.NFA.Basic

open NFA

namespace Zero

variable {σ : Type _} (q₁ q₂ : Type _) {σs : Finset σ}  [DecidableEq q₁] [DecidableEq q₂] [DecidableEq σ]

def zeroNfa : NFA σs := {q := Nat, qs := {}, q₀ := {}, fs := {}, δ := fun _ _ => {}}

theorem not_accepts (w : word σs) : ¬nfa_accepts zeroNfa w := by
  intro acc
  simp only [nfa_accepts,zeroNfa,δ_star] at acc
  rw [δ_star'_empty,Finset.Nonempty] at acc
  apply Exists.elim acc
  intro x xin
  rw [Finset.mem_inter] at xin
  apply Finset.not_mem_empty
  apply xin.1

end Zero

import Mathlib.Data.Finset.Sum
import Mathlib.Logic.Embedding.Basic
import Automaton.NFA.Basic

open NFA

namespace Zero

variable {σ : Type _} (q₁ q₂ : Type _) {σs : Finset σ}  [DecidableEq q₁] [DecidableEq q₂] [DecidableEq σ]

def zeroNfa : NFA σs := {q := Nat, qs := {}, q₀ := {}, fs := {}, δ := fun _ _ => {}}

theorem accepts_iff (w : word σs) : nfa_accepts zeroNfa w ↔ False := by
  apply Iff.intro
  · intro na
    simp only [zeroNfa,nfa_accepts,Finset.Nonempty] at na
    apply Exists.elim na
    intro x xin
    rw [Finset.mem_inter] at xin
    apply Finset.not_mem_empty
    exact xin.2
  · intro f
    trivial

end Zero

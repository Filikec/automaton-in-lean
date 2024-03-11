import Mathlib.Data.Finset.Sum
import Mathlib.Logic.Embedding.Basic
import Automaton.NFA.Basic

open NFA

namespace Empty

variable {σ : Type _} {q₁ q₂ : Type _} {σs : Finset σ}  [DecidableEq q₁] [DecidableEq q₂] (t : NFA σs ) [DecidableEq σ]


def empty : NFA σs := {qs := {1} , q₀ := {⟨1,by simp⟩}, fs := {⟨1,by simp⟩}, δ := fun _ _ => {} }

theorem accepts_iff (w : word σs) : nfa_accepts empty w ↔ w = [] := by
  apply Iff.intro
  · simp only [nfa_accepts]
    intro ne
    match w with
    | [] => rfl
    | e::es => simp only [δ_star,δ_star',empty,δ_step,Finset.singleton_biUnion] at ne
               rw [Finset.Nonempty] at ne
               apply Exists.elim ne
               intro x xin
               rw [δ_star'_empty] at xin
               exfalso
               apply Finset.not_mem_empty
               apply xin
  · intro eq
    rw [eq]
    simp [empty]


end Empty

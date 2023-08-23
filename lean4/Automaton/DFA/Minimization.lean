import Automaton.DFA.Basic
import Automaton.Finset.Basic
import Mathlib.Data.FinEnum

open DFA Finset

namespace DFA

variable {σ : Type _} [FinEnum σ] (t : DFA σ)

@[simp]
def minimization_reachable_q : Finset t.q := by
  have qs := (finenum_to_finset t.q).filter (fun q => reachable t t.init q)
  exact qs.map ⟨  fun q =>  q , by simp [Function.Injective]⟩ 

@[simp]
def minimization_reachable_init : { x // x ∈ minimization_reachable_q t } := by
  exact ⟨t.init , by simp [finenum_to_finset]; apply reachable.base; exact t.init⟩ 

@[simp]
def minimization_reachable_fs : Finset {x // x ∈ minimization_reachable_q t} := by
  apply Finset.attach

@[simp]
def minimization_reachable_δ : { x // x ∈ minimization_reachable_q t } → σ → { x // x ∈ minimization_reachable_q t } := by
  intro q e
  have := q.2
  simp [finenum_to_finset] at this
  exact ⟨ t.δ q e, by simp [finenum_to_finset]; apply reachable.step; exact this⟩ 

def minimization_reachable : DFA σ := 
  {q := minimization_reachable_q t, init := minimization_reachable_init t, fs := minimization_reachable_fs t, δ := minimization_reachable_δ t}

theorem minimization_reachable_δ_star'_eq (w : word σ) : (q : t.q) → (r : reachable t t.init q) → δ_star' t q w = (δ_star' (minimization_reachable t) ⟨q, by simp [finenum_to_finset]; exact r⟩  w).1 := by
  induction w with
  | nil => simp
  | cons a as s => simp only [δ_star']
                   intro q r
                   rw [s]
                   simp [minimization_reachable]
                   apply reachable.step
                   exact r

                   
                   
            



    
    

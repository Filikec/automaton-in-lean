import Automaton.DFA.Basic
import Automaton.Finset.Basic
import Mathlib.Data.FinEnum

open DFA Finset

namespace DFA

variable {σ : Type _} [FinEnum σ] (t : DFA σ)

@[simp]
def minimization_reachable_q : Finset t.q := by
  have qs := (finenum_to_finset t.q).filter (fun q => reachable t t.init q)
  exact qs

@[simp]
def minimization_reachable_init : { x // x ∈ minimization_reachable_q t } := by
  exact ⟨t.init , by simp [finenum_to_finset]; apply reachable.base; exact t.init⟩ 

@[simp]
def minimization_reachable_fs : Finset {x // x ∈ minimization_reachable_q t} := by
  have := Finset.attach (minimization_reachable_q t)
  exact this.filter (fun q => q.1 ∈ t.fs)


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

theorem minimization_reachable_δ_star_eq (w : word σ) : δ_star t w = (δ_star (minimization_reachable t) w).1 := by
  simp only [δ_star]
  apply minimization_reachable_δ_star'_eq
  exact reachable.base t.init

theorem minimization_reachable_eq (w : word σ) : dfa_accepts t w ↔ dfa_accepts (minimization_reachable t) w := by
  apply Iff.intro
  · intro dfa
    simp only [dfa_accepts] at dfa
    simp only [dfa_accepts] 
    simp [minimization_reachable]
    rw [minimization_reachable_δ_star_eq] at dfa
    simp [minimization_reachable] at dfa
    exact dfa
  · intro dfa
    simp only [dfa_accepts] at dfa
    simp only [dfa_accepts] 
    rw [minimization_reachable_δ_star_eq] 
    simp [minimization_reachable] at dfa
    simp [minimization_reachable]
    exact dfa

  
    
    
    
    
    
  



    
          
                   
            



    
    

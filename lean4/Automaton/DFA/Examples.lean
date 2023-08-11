import Automaton.DFA.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic

/-!
  Concrete examples of DFA
-/

open Nat DFA


def δ₁ : Fin 2 → Fin 2 → Fin 2
  | 0 , 1 => 1
  | 0 , 0 => 0
  | 1 , 1 => 1
  | 1 , 0 => 0

-- accepts all words that end with '1'
def last_is_one : DFA (Fin 2) := {q := Fin 2, init := 0 , fs := {1} , δ := δ₁}

def w₁ : word (Fin 2) := [ 1, 0 ]
def w₂ : word (Fin 2) := [ 0 ,1 ]
def w₃ : word (Fin 2) := [ ]

theorem accepts_all_last_1 (w : word (Fin 2)) : dfa_accepts last_is_one (w ++ [1]) := by
  apply accepts_suffix_if
  intro q r
  simp [last_is_one]
  simp [last_is_one] at q
  match q with
  | 0 => simp
  | 1 => simp


#eval δ_star' last_is_one last_is_one.init w₁ -- 0
#eval dfa_accepts last_is_one w₁ -- false

#eval δ_star last_is_one w₂ -- 1
#eval dfa_accepts last_is_one w₂ -- true

#eval δ_star last_is_one w₃ -- 0
#eval dfa_accepts last_is_one w₃ -- false

-- accepts all words that start with 1
def δ₂ : Fin 3 → Fin 2 → Fin 3
  | 0 , 1 => 1
  | 0 , 0 => 2
  | 1 , 1 => 1
  | 1 , 0 => 1
  | _ , _ => 2

def first_is_one : DFA (Fin 2) := {q := Fin 3, init := 0, fs := {1} , δ := δ₂}

theorem accepts_all_first_1 (w : word (Fin 2)) : dfa_accepts first_is_one ([1] ++ w) := by
  apply accepts_prefix_if
  intro q r
  induction r with
  | base => simp
  | step qc rqc e s => simp [first_is_one] at s            
                       rw [s]
                       match e with
                       | 0 => simp
                       | 1 => simp
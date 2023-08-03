import Automaton.DFA.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic

/-!
  Concrete examples of DFA
-/

open Nat DFA


def trans_fun : Fin 2 → Fin 2 → Fin 2
  | 0 , 1 => 1
  | 0 , 0 => 0
  | 1 , 1 => 1
  | 1 , 0 => 0

-- accepts all words that end with '1'
def last_is_one : DFA (Fin 2) := {q := Fin 2, init := 0 , fs := {1} , δ := trans_fun}

def w₁ : word (Fin 2) := [ 1, 0 ]
def w₂ : word (Fin 2) := [ 0 ,1 ]
def w₃ : word (Fin 2) := [ ]


#eval δ_star' last_is_one last_is_one.init w₁ -- 0
#eval dfa_accepts last_is_one w₁ -- false

#eval δ_star last_is_one w₂ -- 1
#eval dfa_accepts last_is_one w₂ -- true

#eval δ_star last_is_one w₃ -- 0
#eval dfa_accepts last_is_one w₃ -- false

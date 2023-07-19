import Automaton.DFA.Basic

/-!
  Concrete examples of DFA
-/

open Nat DFA

def trans_fun : Nat → Char → Nat
  | 0 , '0' => 0
  | 0 , '1' => 1
  | 1 , '0' => 0
  | 1 , '1' => 1
  | _ , _ => 2

-- 1 is the only final state
def fin_states : Set Nat := fun n => n = 1

-- the membership of a set of fin states must be decidable for the language 
-- to be decidable
instance : DecidablePred (fin_states) := by
  intro n
  dsimp [fin_states]
  cases n with
  | zero => apply Decidable.isFalse ; trivial
  | succ n => cases n with
    | zero => apply Decidable.isTrue ; trivial
    | succ n => apply Decidable.isFalse
                simp
                apply Nat.succ_ne_zero

def last_is_one : DFA := {q := Nat , init := 0 , fs := fin_states , σ := Char , δ := trans_fun}

def w1 : word last_is_one.σ := [ '1','0' ]
def w2 : word last_is_one.σ := [ '0','1' ]
def w3 : word last_is_one.σ := [ ]

#eval δ_star last_is_one w1 last_is_one.init -- 0
#eval accepts last_is_one w1 -- false

#eval δ_star last_is_one w2 last_is_one.init -- 1
#eval accepts last_is_one w2 -- true

#eval δ_star last_is_one w3 last_is_one.init -- 0
#eval accepts last_is_one w3 -- false
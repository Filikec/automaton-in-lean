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



def states : Finset Nat := {0 , 1 , 2}

-- 1 is the only final state
def fin_states : Finset Nat := {1}


-- accepts all words that end with '1'
def last_is_one : DFA Nat Char := {q := states , init := 0 , fs := fin_states , δ := trans_fun}

-- words are consumed backwwards, see definition of δ_star
def w1 : word Char := [ '1','0' ]
def w2 : word Char := [ '0','1' ]
def w3 : word Char := [ ]


#eval δ_star last_is_one w1 -- 1
#eval dfa_accepts last_is_one w1 -- true

#eval δ_star last_is_one w2 -- 0
#eval dfa_accepts last_is_one w2 -- false

#eval δ_star last_is_one w3 -- 0
#eval dfa_accepts last_is_one w3 -- false

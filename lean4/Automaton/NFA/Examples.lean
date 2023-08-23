import Automaton.NFA.Basic
import Automaton.DFA.ToNFA
import Automaton.NFA.ToDFA

-- normal automaton

open NFA DFA

def δ₁ : Fin 2 → Fin 2 → Finset (Fin 2)
  | 0 , 1 => {1}
  | 0 , 0 => {0}
  | 1 , 1 => {1}
  | 1 , 0 => {0}

def nfa₁ : NFA (Fin 2) := {q := Fin 2, init := 0 , fs := {1} , δ := δ₁}

def w₁ : word (Fin 2) := []
def w₂ : word (Fin 2) := [1 , 0]
def w₃ : word (Fin 2) := [0 , 1]

#eval nfa_accepts nfa₁ w₁
#eval nfa_accepts nfa₁ w₂
#eval nfa_accepts nfa₁ w₃

#eval dfa_accepts (ToDFA.nfa_to_dfa nfa₁) w₁
#eval dfa_accepts (ToDFA.nfa_to_dfa nfa₁) w₂
#eval dfa_accepts (ToDFA.nfa_to_dfa nfa₁) w₃

#eval nfa_accepts (ToNFA.dfa_to_nfa (ToDFA.nfa_to_dfa nfa₁)) w₁
#eval nfa_accepts (ToNFA.dfa_to_nfa (ToDFA.nfa_to_dfa nfa₁)) w₂
#eval nfa_accepts (ToNFA.dfa_to_nfa (ToDFA.nfa_to_dfa nfa₁)) w₃

-- all strings ending with 01
def δ₂ : Fin 4 → Fin 2 → Finset (Fin 4)
  | 0 , 0 => {0 , 1}
  | 0 , 1 => {0}
  | 1 , 0 => {3}
  | 1 , 1 => {2}
  | _ , _ => {3}

def nfa₂ : NFA (Fin 2) := {q := Fin 4, init := 0 , fs := {2} , δ := δ₂}

def w₄ : word (Fin 2) := [0 , 1]
def w₅ : word (Fin 2) := [1 , 0 , 0 , 1]
def w₆ : word (Fin 2) := [1 , 0]
def w₇ : word (Fin 2) := [1 , 1]

#eval nfa_accepts nfa₂ w₄
#eval nfa_accepts nfa₂ w₅
#eval nfa_accepts nfa₂ w₆
#eval nfa_accepts nfa₂ w₇
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Automaton.DFA.Basic
import Automaton.DFA.Minimization

/-!
  Concrete examples of DFA
-/

open Nat DFA

-- need to be able to synth FinEnum to print the DFA
def Q : Finset (Fin 2) := {0,1}
def σ : Finset (Fin 2) := {0,1}

def δ₁ : Q → σ → Q
  | ⟨0,_⟩ , ⟨0,_⟩ => ⟨1, by simp⟩
  | ⟨0,_⟩ , ⟨1,_⟩ => ⟨0, by simp⟩
  | ⟨1,_⟩ , ⟨0,_⟩ => ⟨1, by simp⟩
  | ⟨1,_⟩ , ⟨1,_⟩ => ⟨0, by simp⟩

-- accepts all words that end with '1'
def last_is_one : DFA σ  := {qs := Q, q₀ := ⟨0, by simp⟩ , fs := {⟨1 , by simp⟩} , δ := δ₁}

def w₁ : word Q := [ ⟨1 , by simp⟩, ⟨0 , by simp⟩ ]
def w₂ : word Q := [ ⟨0 , by simp⟩, ⟨1 , by simp⟩ ]
def w₃ : word Q := [ ]

#eval dfa_accepts last_is_one w₁
#eval dfa_accepts last_is_one w₂
#eval dfa_accepts last_is_one w₃

def q₁ : Q := ⟨0, by simp⟩
def q₂ : Q := ⟨1, by simp⟩

#eval distinct_table_filling last_is_one q₁ q₂
#eval distinct_table_filling last_is_one q₁ q₁

#eval distinct last_is_one q₁ q₂
#eval distinct last_is_one q₁ q₁

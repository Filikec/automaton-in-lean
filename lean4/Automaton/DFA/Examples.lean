import Automaton.DFA.Basic
import Automaton.DFA.Minimization
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic

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
def last_is_one : @DFA (Fin 2) (Fin 2) := {qs := Q, σs := σ , init := ⟨0, by simp⟩ , fs := {⟨1 , by simp⟩} , δ := δ₁}

def w₁ : word (Fin 2) := [ 1, 0 ]
def w₂ : word (Fin 2) := [ 0, 1 ]
def w₃ : word (Fin 2) := [ ]

#eval last_is_one

def q₁ : last_is_one.qs := ⟨0, by simp⟩
def q₂ : last_is_one.qs := ⟨1, by simp⟩

#eval distinct_table_filling q₁ q₂
#eval distinct_table_filling q₁ q₁

#eval distinct q₁ q₂
#eval distinct q₁ q₁

import Automaton.DFA.Basic
import Automaton.DFA.Minimization
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic

/-!
  Concrete examples of DFA
-/

open Nat DFA


def δ₁ : { x : Fin 2 // x ∈ ({0 , 1} : Finset (Fin 2)) } → { x : Fin 2 // x ∈ ({0 , 1} : Finset (Fin 2)) } → { x : Fin 2 // x ∈ ({0 , 1} : Finset (Fin 2))}
  | ⟨0,_⟩ , ⟨1,_⟩ => ⟨1, by simp⟩
  | ⟨0,_⟩ , ⟨0,_⟩ => ⟨0, by simp⟩
  | ⟨1,_⟩ , ⟨1,_⟩ => ⟨1, by simp⟩
  | ⟨1,_⟩ , ⟨0,_⟩ => ⟨0, by simp⟩

-- accepts all words that end with '1'
def last_is_one : DFA (Fin 2) (Fin 2) := {qs := {0, 1}, σs := {0,1}, init := ⟨0,by simp⟩ , fs := {⟨1 , by simp⟩} , δ := δ₁}

def w₁ : word (Fin 2) := [ 1, 0 ]
def w₂ : word (Fin 2) := [ 0, 1 ]
def w₃ : word (Fin 2) := [ ]

#eval last_is_one

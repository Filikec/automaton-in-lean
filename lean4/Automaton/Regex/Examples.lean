import Automaton.Regex.Regex2NFA
import Automaton.Regex.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic

open Regex

def f (n : ℕ) : Finset (Fin n) := (Fin.fintype n).elems

instance [NeZero n] : OfNat ({x  // x ∈ f n}) a where
  ofNat := ⟨Fin.ofNat' a (NeZero.pos n), by simp [f,Fintype.complete]⟩

def r₁ : Regex (f 3) := ((Regex.char 0) * (Regex.char 1)) + (Regex.char 2)

#eval [0,1] ∈ regexLan r₁
#eval [1] ∈ regexLan r₁
#eval [2] ∈ regexLan r₁

def r₂ : Regex (f 3) := (Regex.star ((Regex.char 0) * (Regex.char 1))) + (Regex.char 2)

#eval [0,1] ∈ regexLan r₂
#eval [1] ∈ regexLan r₂
#eval [2] ∈ regexLan r₂
#eval [] ∈ regexLan r₂
#eval [0,1,0,1] ∈ regexLan r₂

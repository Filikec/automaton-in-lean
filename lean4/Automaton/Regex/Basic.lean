import Automaton.Language.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic

namespace Regex

open Set Finset

inductive Regex (f : Finset α) : Type u
  | zero : Regex f
  | epsilon : Regex f
  | char : (α : f) → Regex f
  | plus : Regex f → Regex f → Regex f
  | append : Regex f → Regex f → Regex f
  | star : Regex f → Regex f

open Regex

variable {α : Type _} [DecidableEq α] (f : Finset α)

inductive plusLang (P : Lang α) : Lang α where
| empty :  ∀ w ∈ P, plusLang P w
| extend : ∀ u w, P u → plusLang P w → plusLang P (u ++ w)

inductive starLang (P : Lang α) : Lang α where
| empty : starLang P []
| extend : ∀ u w, P u → starLang P w → starLang P (u ++ w)

def RegexLan : Regex f → Lang f
  | zero => ∅
  | epsilon => {[]}
  | char a => {[a]}
  | plus a b => RegexLan a ∪ RegexLan b
  | append a b => {w | ∃ x y, x ∈ RegexLan a ∧ y ∈ RegexLan b ∧ w = x++y}
  | star a => starLang (RegexLan a)



end Regex

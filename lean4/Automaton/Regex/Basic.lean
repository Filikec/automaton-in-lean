import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Automaton.Language.Basic


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

lemma ex_cons_eq (w : List α) : ∃ a b : List α, a ++ b = w := by
  induction w with
  | nil => exists []
           exists []
  | cons e es s => apply Exists.elim s
                   intro a ex
                   apply Exists.elim ex
                   intro b h
                   exists e::a
                   exists b
                   rw [←h]
                   rfl

inductive plusLang (P : Lang α) : Lang α where
| empty :  ∀ w ∈ P, plusLang P w
| extend : ∀ u w, P u → plusLang P w → plusLang P (u ++ w)

inductive starLang (P : Lang α) : Lang α where
| empty : starLang P []
| extend : ∀ u w, P u → starLang P w → starLang P (u ++ w)

theorem plusLang_ss_starLang : plusLang p ⊆ starLang p := by
  rw [Set.subset_def]
  intro x xin
  induction xin with
  | empty h => have : h = h ++ [] := by simp
               rw [this]
               apply starLang.extend
               · assumption
               · apply starLang.empty
  | extend a b pa _ s => apply starLang.extend
                         · assumption
                         · apply s

def RegexLan : Regex f → Lang f
  | zero => ∅
  | epsilon => {[]}
  | char a => {[a]}
  | plus a b => RegexLan a ∪ RegexLan b
  | append a b => {w | ∃ x y, x ∈ RegexLan a ∧ y ∈ RegexLan b ∧ w = x++y}
  | star a => starLang (RegexLan a)


end Regex

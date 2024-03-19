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


theorem if_mem_starLang : w ∈ starLang P → (w = [] ∨ ∃ a b, a ≠ [] ∧ a++b=w ∧ a ∈ P ∧ b ∈ starLang P) := by
  intro win
  induction win with
  | empty => apply Or.inl; rfl
  | extend a b pa sb s => apply Or.elim s
                          · intro beq
                            match a with
                            | [] => apply Or.inl; rw [beq]; rfl
                            | a::as => apply Or.inr
                                       exists a::as
                                       exists b
                                       use by simp, rfl, pa
                                       rw [beq]
                                       exact starLang.empty
                          · intro ex
                            apply Exists.elim ex
                            intro a' ex
                            apply Exists.elim ex
                            intro b' h
                            apply Or.inr
                            match a with
                            | [] => exists a'
                            | a::as => exists a::as
                                       exists a'++b'
                                       use by simp
                                       rw [h.2.1]
                                       use rfl, pa
                                       exact sb

theorem mem_starLang_if : (w = [] ∨ ∃ a b, a ≠ [] ∧ a++b=w ∧ a ∈ P ∧ b ∈ starLang P) → w ∈ starLang P := by
  intro h
  apply Or.elim h
  · intro eq
    rw [eq]
    apply starLang.empty
  · intro ex
    apply Exists.elim ex
    intro a ex
    apply Exists.elim ex
    intro b h
    rw [←h.2.1]
    apply starLang.extend
    · apply h.2.2.1
    · apply h.2.2.2


theorem mem_starLang_iff : w ∈ starLang P ↔ (w = [] ∨ ∃ a b, a ≠ [] ∧ a++b=w ∧ a ∈ P ∧ b ∈ starLang P) := by
  apply Iff.intro
  · apply if_mem_starLang
  · apply mem_starLang_if

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

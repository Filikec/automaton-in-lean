import Automaton.Language.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Automaton.NFA.ENFA

namespace Regex

open Set Finset εNFA

inductive Regex (f : Finset α) : Type u
  | zero : Regex f
  | epsilon : Regex f
  | char : (α : f) → Regex f
  | plus : Regex f → Regex f → Regex f
  | append : Regex f → Regex f → Regex f
  | star : Regex f → Regex f

open Regex

variable {α : Type _} [DecidableEq α] (f : Finset α)

inductive starLang (l : Lang f) : Lang f where
  | empty : starLang l []
  | star  : ∀ u w : List f, u ∈ l → w ∈ l → starLang l (u++w)

def RegexLan : Regex f → Lang f
  | zero => ∅
  | epsilon => {[]}
  | char a => {[a]}
  | plus a b => RegexLan a ∪ RegexLan b
  | append a b => {w | ∃ x y, x ∈ RegexLan a ∧ y ∈ RegexLan b ∧ w = x++y}
  | star a => starLang f (RegexLan a)


def ZeroεNFA : εNFA f {0} := {q₀ := {⟨0,by simp⟩} , fs := {} , δ := fun _ _ => {⟨0,by simp⟩}}
def EpsilonεNFA : εNFA f {0} := {q₀ := {⟨0,by simp⟩} , fs := {⟨0,by simp⟩} , δ := fun _ _ => ∅}
def CharεNFA (c : f) : εNFA f {0,1} := {q₀ := {⟨0,by simp⟩} , fs := {⟨1,by simp⟩} , δ := fun q e => if q = ⟨0,by simp⟩ ∧ e = c then {⟨1,by simp⟩} else ∅}


lemma ZeroεNFALang : εNFA_lang (ZeroεNFA f) = ∅ := by
  simp only [εNFA_lang,εnfa_accepts,ZeroεNFA,Finset.inter_empty]
  trivial


lemma EpsilonεNFALang : εnfa_accepts (EpsilonεNFA f) w ↔ w = [] := by
  apply Iff.intro
  · intro ac
    simp only [εnfa_accepts,EpsilonεNFA] at ac
    match w with
    | [] => simp
    | e::es => simp only [δ_star,δ_star',Finset.Nonempty] at ac
               apply Exists.elim ac
               intro w win
               simp [δ_step,Finset.biUnion] at win
               rw [εNFA_δ_star'_empty] at win
               simp
               apply Finset.not_mem_empty
               exact win.1
  · intro w
    rw [w]
    simp [εnfa_accepts,δ_star,δ_star',EpsilonεNFA,Finset.Nonempty]
    apply εclosure_start_mem
    simp







end Regex

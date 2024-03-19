import Mathlib.Data.Finset.Sum
import Mathlib.Logic.Embedding.Basic
import Automaton.NFA.Basic

open NFA


namespace Char

variable {σ : Type _} {q₁ q₂ : Type _} {σs : Finset σ}  [DecidableEq q₁] [DecidableEq q₂] (t s : NFA σs )[DecidableEq σ]

def char_qs : Finset ℕ := {1,2}

def char_δ (a : σs) : char_qs → σs → Finset char_qs
  | ⟨1, _⟩ , s => if s = a then {⟨2, by simp⟩} else {}
  | _ , _ => {}

def char (a : σs) : NFA σs := {qs := char_qs, q₀ := {⟨1,by simp⟩}, fs := {⟨2,by simp⟩}, δ := char_δ a }

theorem accepts_iff (a : σs) : nfa_accepts (char a) w ↔ w = [a] := by
  simp only [nfa_accepts,char]
  apply Iff.intro
  · intro ne
    rw [Finset.Nonempty] at ne
    apply Exists.elim ne
    intro x xin
    simp only [char_δ] at xin
    match w with
    | [] => simp [δ_star,δ_star'] at xin
    | e::es => simp only [δ_star,δ_star',δ_step,Finset.singleton_biUnion] at xin
               split at xin
               · have : e = a := by assumption
                 rw [this]
                 match es with
                 | [] => rfl
                 | e'::es' => simp only [δ_star,δ_star',δ_step,Finset.singleton_biUnion] at xin
                              rw [δ_star'_empty,Finset.mem_inter] at xin
                              exfalso
                              apply Finset.not_mem_empty
                              apply xin.1
               · rw [δ_star'_empty,Finset.mem_inter] at xin
                 exfalso
                 apply Finset.not_mem_empty
                 apply xin.1
  · intro eq
    rw [eq]
    simp [δ_star,δ_star',δ_step,Finset.singleton_biUnion,char_δ]




end Char

import Automaton.Language.Basic
import Mathlib.Data.Finset.Basic

/-!
  This file contains the definition of a DFA as well as a few fundamental operations it can do
  * `δ_star` and `accepts` functions.
  * Asserts the decidability of the language of DFA
  * Provides a definition for equality of DFA and proves basic properties about the equality
    * Two DFAs are equal, if they accept the same language
-/

namespace DFA


-- can replace Nat with a type that has decidable equality
structure DFA (σ : Type _) where
  q : Finset Nat        -- finite set of states
  init : Nat            -- initial state
  fs : Finset Nat       -- accepting states
  δ : Nat → σ → Nat     -- transition function

variable {σ : Type _ } (r s t : DFA σ)


-- δ* function
-- the state reached after following all transitions given a word
-- the first letter in list is the last character consumed
def δ_star : (w : word σ) → Nat
  | [] => t.init
  | e :: es => t.δ (δ_star es) e

-- whether a DFA accepts a word
def dfa_accepts : (w : word σ) → Prop := by
  intro w
  have f := δ_star t w
  exact f ∈ t.fs

def dfaLang : Lang σ := fun w => dfa_accepts t w

-- DFA language is decidable
instance decidableLang (w : word σ) : Decidable (dfa_accepts t w) := by
  dsimp [dfa_accepts]
  apply Finset.decidableMem

-- equality of DFAs
def eq : Prop := ∀ w : word σ , dfa_accepts t w ↔ dfa_accepts s w

private theorem eq.refl : eq t t := by
  dsimp [eq]
  intro w
  apply Iff.intro <;> (intro ; assumption) 

private theorem eq.trans : eq t s → eq s r → eq t r := by
  intro eq₁ eq₂
  dsimp [eq] at eq₁ eq₂
  dsimp [eq]
  intro w
  apply Iff.intro
  · intro r
    apply (Iff.mp (eq₁ w))
    apply (Iff.mp (eq₂ w))
    exact r
  · intro t
    apply (Iff.mpr (eq₂ w))
    apply (Iff.mpr (eq₁ w))
    exact t

private theorem eq.sym : eq t s → eq s t := by
  intro h
  dsimp [eq]
  dsimp [eq] at h
  intro w
  apply Iff.intro 
  <;> intro 
  <;> (first | apply (Iff.mp (h w)) | apply (Iff.mpr (h w))) 
  <;> assumption

-- dfa accepts nil iff init is final
theorem dfa_accepts_nil_iff_final : dfa_accepts t [] ↔ t.init ∈ t.fs := by
  apply Iff.intro 
  <;> intro h 
  <;> (first |  dsimp [dfa_accepts])
  <;> exact h

end DFA
import Automaton.Language.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.FinEnum
import Automaton.Finset.Basic

/-!
  This file contains the definition of a DFA as well as a few fundamental operations it can do
  * `δ_star` and `accepts` functions.
  * Asserts the decidability of the language of DFA
  * Provides a definition for equality of DFA and proves basic properties about the equality
    * Two DFAs are equal, if they accept the same language
  * Provides an inductive definition of `reachable` - all states that can be reached from a state
  * Contains some lemmas and theorems that provide an easier way to prove things about accepted langs
  * Main theorems about languages : `accepts_prefix_iff` , `accepts_suffix_iff`
-/

namespace DFA


structure DFA (σ : Type _) where
  q : Type _             -- states
  init : q               -- initial state
  fs : Finset q          -- accepting states
  δ : q → σ → q          -- transition function
  [fq : FinEnum q]
  [fσ : FinEnum σ]

variable {σ : Type _} [FinEnum σ] (r s t : DFA σ)

instance : FinEnum t.q := t.fq

-- δ* function
-- the state reached after following all transitions given a word
-- the first letter in list is the last character consumed
@[simp]
def δ_star' (q : t.q) : (w : word σ) → t.q
  | [] => q
  | e :: es => δ_star' (t.δ q e) es 


def δ_star : (w : word σ) → t.q := δ_star' t t.init

-- whether a DFA accepts a word
@[simp]
def dfa_accepts : (w : word σ) → Prop := by
  intro w
  exact δ_star t w ∈ t.fs

def dfaLang : Lang σ := fun w => dfa_accepts t w


-- all states reachable from current state
inductive reachable (q : t.q) : t.q → Prop where
  | base (q' : t.q) : reachable q q
  | step (q' : t.q) : reachable q q' → ∀ e : σ , reachable q (t.δ q' e)


instance : DecidableRel (reachable t) := sorry


-- DFA language is decidable
instance decidableLang (w : word σ) : Decidable (dfa_accepts t w) := by
  simp [dfa_accepts]
  have : DecidableEq t.q := by exact t.fq.decEq  
  apply Finset.decidableMem
  
-- equality of DFAs
def eq : Prop := ∀ w : word σ , dfa_accepts t w ↔ dfa_accepts s w

private theorem eq.refl : eq t t := by
  intro w
  apply Iff.intro <;> (intro ; assumption) 

private theorem eq.trans : eq t s → eq s r → eq t r := by
  intro eq₁ eq₂
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
  intro w
  apply Iff.intro 
  <;> intro 
  <;> (first | apply (Iff.mp (h w)) | apply (Iff.mpr (h w))) 
  <;> assumption


-- dfa accepts nil iff init is final
theorem dfa_accepts_nil_iff_final : dfa_accepts t [] ↔ t.init ∈ t.fs := by
  apply Iff.intro 
  <;> intro h 
  <;> (first | simp [dfa_accepts])
  <;> exact h

lemma δ_δ_star'_concat_eq_δ_star' : (q : t.q) → DFA.δ t (δ_star' t q l) a = δ_star' t q (l ++ [a]) := by
  induction l with
  | nil => simp
  | cons e es s => intro q
                   simp only [δ_star',List.append_eq]
                   apply s (DFA.δ t q e)

theorem δ_star_append_eq (r : word σ) : (l : word σ) → δ_star t (l++r) = δ_star' t (δ_star t l) r := by
  induction r with
  | nil => simp
  | cons a as s => intro l
                   have : l ++ a :: as = l ++ [a] ++ as := by simp
                   rw [this,s]
                   simp [δ_star,δ_δ_star'_concat_eq_δ_star']



lemma δ_star'_reachable (w : word σ) (q : t.q) : (q' : t.q) → reachable t q q' → reachable t q (δ_star' t q' w) := by
  induction w with
  | nil => simp [δ_star]
  | cons e es s => intro q' rq' 
                   rw [δ_star']
                   apply s
                   apply reachable.step
                   exact rq'

theorem accepts_from_state_if (w : word σ) (q : t.q) : (∀ q' : t.q , (reachable t q q' → q' ∈ t.fs)) → δ_star' t q w ∈ t.fs := by
  intro q'
  apply q'
  apply δ_star'_reachable
  exact reachable.base q

theorem state_reachable_iff (q q' : t.q) : reachable t q q' ↔ ∃ w : word σ , δ_star' t q w = q' := by
  apply Iff.intro
  · intro rq'
    induction rq' with
    | base => exists []
    | step qc _ e s => apply Exists.elim s
                       intro w δ'
                       exists List.concat w e
                       simp [List.concat_eq_append,←δ_δ_star'_concat_eq_δ_star',δ']
  · intro ex
    apply Exists.elim ex
    intro w δ'
    simp only [δ_star'] at δ' 
    rw [←δ']
    apply δ_star'_reachable
    exact reachable.base q

theorem accepts_prefix_if (l r : word σ) : (∀ q' : t.q , (reachable t (δ_star t l) q' → q' ∈ t.fs)) → dfa_accepts t (l ++ r) := by
  intro fa
  rw [dfa_accepts,δ_star_append_eq]
  apply accepts_from_state_if
  intro q' rq'
  apply fa
  exact rq'

-- To prove that DFA accepts any word starting with a prefix
-- If after l, a state is reached from which all combinations of transitions lead
-- to a final state, it always
theorem accepts_prefix_iff (p : word σ) : dfa_accepts t p ∧ (∀ q' : t.q , (reachable t (δ_star t p) q' → q' ∈ t.fs)) ↔ ∀ s : word σ , dfa_accepts t (p ++ s) := by
  apply Iff.intro
  · intro h s
    apply accepts_prefix_if
    apply h.2
  · intro h
    simp only [dfa_accepts] at h
    apply And.intro
    · have : p = p ++ [] := by simp
      rw [this]
      apply h
    · intro q' r
      have := Iff.mp (state_reachable_iff t (δ_star t p) q') r
      apply Exists.elim this
      intro w δ'
      rw [←δ_star_append_eq] at δ'
      rw [←δ']
      exact h w

lemma accepts_suffix_if (l r : word σ) : (∀ q : t.q , reachable t t.init q → δ_star' t q r ∈ t.fs) → dfa_accepts t (l ++ r) := by
  intro fa
  simp only [dfa_accepts]
  rw [δ_star_append_eq]
  apply fa
  apply δ_star'_reachable
  exact reachable.base t.init
  
-- To prove that DFA always accepts some suffix
-- If from any reachable state the word is accepted, it is always accepted
theorem accepts_suffix_iff (s : word σ) : (∀ p : word σ,  dfa_accepts t (p ++ s)) ↔ (∀ q : t.q , reachable t t.init q → δ_star' t q s ∈ t.fs) := by
  apply Iff.intro
  · intro fa q rq
    have := Iff.mp (state_reachable_iff t t.init q) rq
    apply Exists.elim this
    intro w δ'
    rw [←δ']
    have : δ_star' t t.init w = δ_star t w := by simp [δ_star]
    rw [this, ←δ_star_append_eq]
    apply fa
  · intro fa w
    apply accepts_suffix_if
    exact fa

end DFA
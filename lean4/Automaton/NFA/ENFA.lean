import Mathlib.Data.Option.Basic
import Automaton.Language.Basic
import Automaton.Finset.Basic
import Mathlib.Data.Nat.Basic
import Automaton.NFA.Basic
import Mathlib.Data.Finset.Powerset
import Automaton.DFA.Basic
import Automaton.NFA.ToDFA

open NFA Finset DFA

namespace εNFA

structure εNFA (σ : Type _) (q : Type _) where
  σs : Finset σ    -- alphabet
  qs : Finset q    -- states
  init : qs        -- initial state
  fs : Finset qs   -- accepting states
  δ : qs → Option σs → Finset qs -- transition function
  [dq : DecidableEq q]
  [dσ : DecidableEq σ]

variable {σ : Type _} {q : Type _} (r s tn : εNFA σ q) [DecidableEq σ] [DecidableEq q]


-- TODO make εclosure definition better

def εclosure_set : Nat → Finset tn.qs → Finset tn.qs
  | 0 , f => f
  | n+1 , f => (εclosure_set n f).biUnion (fun s => tn.δ s none) ∪ (εclosure_set n f )

def εclosure : tn.qs → Finset tn.qs := fun q => εclosure_set tn tn.qs.card {q}

@[simp]
def fin_εclosure (f : Finset tn.qs) : Finset tn.qs := f.biUnion (fun q => εclosure tn q)

@[simp]
def δ_step (q : Finset tn.qs) (e : tn.σs) : Finset tn.qs := (fin_εclosure tn q).biUnion (fun q' => tn.δ q' e)

def δ_star' (q : Finset tn.qs) : (word tn.σs) → Finset tn.qs
  | [] => fin_εclosure tn q
  | a :: as => δ_star' (δ_step tn q a) as

def δ_star (w : word tn.σs) : Finset tn.qs := δ_star' tn {tn.init} w

def εnfa_accepts (w : word tn.σs) : Prop := (δ_star tn w ∩ tn.fs).Nonempty

instance : Decidable (εnfa_accepts tn w) := by
  simp only [εnfa_accepts]
  apply Finset.decidableNonempty

@[simp]
def εnfa_to_nfa_q : Finset (Finset tn.qs) := tn.qs.attach.powerset

theorem all_in_q (qs : Finset tn.qs) : qs ∈ εnfa_to_nfa_q tn := by
  simp [εnfa_to_nfa_q,finenum_to_finset, · ⊆ ·]

@[simp]
def εnfa_to_nfa_init : { x // x ∈ εnfa_to_nfa_q tn } := ⟨ εclosure tn tn.init , all_in_q tn (εclosure tn tn.init)⟩

@[simp]
def εnfa_to_nfa_fs : Finset { x // x ∈ εnfa_to_nfa_q tn } := by
  have fs := (εnfa_to_nfa_q tn).filter (fun q => (q ∩ tn.fs).Nonempty)
  apply fs.biUnion
  intro q
  exact {⟨q , all_in_q tn q⟩}

@[simp]
def εnfa_to_nfa_δ :  { x // x ∈ εnfa_to_nfa_q tn } → tn.σs → Finset { x // x ∈ εnfa_to_nfa_q tn } := by
  intro q e
  have := fin_εclosure tn (q.1.biUnion (fun q => tn.δ q e))
  exact {⟨ this , all_in_q tn this⟩}

@[simp]
def εnfa_to_nfa : NFA σ (Finset {x // x ∈ tn.qs}) :=
  {qs := εnfa_to_nfa_q tn, σs := tn.σs, init := εnfa_to_nfa_init tn, fs := εnfa_to_nfa_fs tn, δ := εnfa_to_nfa_δ tn}

@[simp]
def εnfa_state_to_nfa_state (q : Finset tn.qs) : Finset ((εnfa_to_nfa tn).qs) := {⟨ q , all_in_q tn q⟩}

theorem δ_star'_eq (w : word tn.σs): (q : Finset tn.qs) → {⟨(εNFA.δ_star' tn q w) , all_in_q tn (εNFA.δ_star' tn q w)⟩} = NFA.δ_star' (εnfa_to_nfa tn) {⟨fin_εclosure tn q , all_in_q tn (fin_εclosure tn q)⟩} w := by
  induction w with
  | nil => simp [δ_star']
  | cons a as s => intro q
                   simp [NFA.δ_star',δ_star',s]

theorem δ_star_eq (w : word tn.σs) : {⟨εNFA.δ_star tn w , all_in_q tn (εNFA.δ_star tn w)⟩ } = NFA.δ_star (εnfa_to_nfa tn) w := by
  simp only [δ_star]
  rw [δ_star'_eq tn w {tn.init}]
  simp

theorem εnfa_to_nfa_eq (w : word tn.σs) : εnfa_accepts tn w ↔ nfa_accepts (εnfa_to_nfa tn) w := by
  simp only [nfa_accepts,εnfa_accepts]
  apply Iff.intro
  · intro a
    rw [←δ_star_eq]
    apply in_nonempty_inter_singleton
    simp [finenum_to_finset]
    apply And.intro
    · simp [· ⊆ ·]
    . exact a
  . intro a
    rw [←δ_star_eq] at a
    have := nonempty_inter_singleton_imp_in ⟨δ_star tn w, all_in_q tn (δ_star tn w)⟩ (εnfa_to_nfa tn).fs
    have := this a
    simp at this
    exact this.2

def εnfa_to_dfa := ToDFA.nfa_to_dfa (εnfa_to_nfa tn)

theorem εnfa_to_dfa_eq : εnfa_accepts tn w ↔ dfa_accepts (εnfa_to_dfa tn) w := by
  simp only [εnfa_to_dfa]
  apply Iff.intro
  · intro e
    have := ToDFA.nfa_to_dfa_eq (εnfa_to_nfa tn) w
    apply this.mp
    have := εnfa_to_nfa_eq tn w
    apply this.mp
    exact e
  · intro e
    have := εnfa_to_nfa_eq tn w
    apply this.mpr
    have := ToDFA.nfa_to_dfa_eq (εnfa_to_nfa tn) w
    apply this.mpr
    exact e

end εNFA

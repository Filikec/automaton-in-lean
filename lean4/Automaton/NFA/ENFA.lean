import Mathlib.Data.FinEnum
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

structure εNFA (σ : Type _) where
  q : Type _                    -- states
  init : q                      -- initial state
  fs : Finset q                 -- accepting states
  δ : q → Option σ → Finset q   -- transition function
  [fq : FinEnum q]
  [fσ : FinEnum σ]

variable {σ : Type _} [FinEnum σ] (tn : εNFA σ)


instance : FinEnum tn.q := tn.fq

-- TODO make εclosure definition better 

def εclosure_set : Nat → Finset tn.q → Finset tn.q 
  | 0 , f => f
  | n+1 , f => (εclosure_set n f).biUnion (fun s => tn.δ s none) ∪ (εclosure_set n f )

def εclosure : tn.q → Finset tn.q := fun q => εclosure_set tn tn.fq.card {q}

@[simp]
def fin_εclosure (f : Finset tn.q) : Finset tn.q := f.biUnion (fun q => εclosure tn q)

@[simp]
def δ_step (q : Finset tn.q) (e : σ) : Finset tn.q := (fin_εclosure tn q).biUnion (fun q' => tn.δ q' e)

def δ_star' (q : Finset tn.q) : (word σ) → Finset tn.q 
  | [] => fin_εclosure tn q
  | a :: as => δ_star' (δ_step tn q a) as

def δ_star (w : word σ) : Finset tn.q := δ_star' tn {tn.init} w

def εnfa_accepts (w : word σ) : Prop := (δ_star tn w ∩ tn.fs).Nonempty

instance : Decidable (εnfa_accepts tn w) := by
  simp only [εnfa_accepts]
  apply Finset.decidableNonempty

@[simp]
def εnfa_to_nfa_q : Finset (Finset tn.q) := (finenum_to_finset tn.q).powerset

theorem all_in_q (qs : Finset tn.q) : qs ∈ εnfa_to_nfa_q tn := by
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
def εnfa_to_nfa_δ :  { x // x ∈ εnfa_to_nfa_q tn } → σ → Finset { x // x ∈ εnfa_to_nfa_q tn } := by
  intro q e
  have := fin_εclosure tn (q.1.biUnion (fun q => tn.δ q e))
  exact {⟨ this , all_in_q tn this⟩}

@[simp]
def εnfa_to_nfa : NFA σ := 
  {q := εnfa_to_nfa_q tn, init := εnfa_to_nfa_init tn, fs := εnfa_to_nfa_fs tn, δ := εnfa_to_nfa_δ tn}

@[simp]
def εnfa_state_to_nfa_state (q : Finset tn.q) : Finset ((εnfa_to_nfa tn).q) := {⟨ q , all_in_q tn q⟩}

theorem δ_star'_eq (w : word σ): (q : Finset tn.q) → {⟨(εNFA.δ_star' tn q w) , all_in_q tn (εNFA.δ_star' tn q w)⟩} = NFA.δ_star' (εnfa_to_nfa tn) {⟨fin_εclosure tn q , all_in_q tn (fin_εclosure tn q)⟩} w := by
  induction w with
  | nil => simp [δ_star']
  | cons a as s => intro q
                   simp only [NFA.δ_star',δ_star',s]
                   rfl

theorem δ_star_eq (w : word σ) : {⟨εNFA.δ_star tn w , all_in_q tn (εNFA.δ_star tn w)⟩ } = NFA.δ_star (εnfa_to_nfa tn) w := by
  simp only [δ_star]
  rw [δ_star'_eq tn w {tn.init}]
  simp


theorem εnfa_to_nfa_eq (w : word σ) : εnfa_accepts tn w ↔ nfa_accepts (εnfa_to_nfa tn) w := by
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

def εnfa_to_dfa : DFA σ := ToDFA.nfa_to_dfa (εnfa_to_nfa tn)

    
end εNFA
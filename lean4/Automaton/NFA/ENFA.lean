import Mathlib.Data.FinEnum
import Mathlib.Data.Option.Basic
import Automaton.Language.Basic
import Automaton.Finset.Basic
import Mathlib.Data.Nat.Basic

namespace NFA


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

def fin_εclosure (f : Finset tn.q) : Finset tn.q := f.biUnion (fun q => εclosure tn q)

def δ_step (q : Finset tn.q) (e : σ) : Finset tn.q := (fin_εclosure tn q).biUnion (fun q' => tn.δ q' e)

def δ_star' (q : Finset tn.q) : (word σ) → Finset tn.q 
  | [] => fin_εclosure tn q
  | a :: as => δ_star' (δ_step tn q a) as

def δ_star (w : word σ) : Finset tn.q := δ_star' tn {tn.init} w

def εnfa_accepts (w : word σ) : Prop := (δ_star tn w ∩ tn.fs).Nonempty

instance : Decidable (εnfa_accepts tn w) := by
  simp only [εnfa_accepts]
  apply Finset.decidableNonempty
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

structure εNFA (σs : Finset σ) where
  q : Type _
  qs : Finset q                  -- states
  q₀ : Finset qs                 -- initial state
  fs : Finset qs                 -- accepting states
  δ : qs → Option σs → Finset qs -- transition function
  [d₁ : DecidableEq q]
  [d₂ : DecidableEq σ]


variable {σ : Type _} {q : Type _} {σs : Finset σ} (tn : εNFA σs) [DecidableEq σ] [DecidableEq q]

instance decEqQ : DecidableEq tn.q := tn.d₁
instance decEq : DecidableEq σ := tn.d₂

def εclosure (f : Finset tn.qs) : Finset tn.qs := by
  let newF := f.biUnion (fun q => tn.δ q none) ∪ f
  if h : f = newF then exact f else exact εclosure newF

termination_by εclosure => tn.qs.card - f.card
decreasing_by simp at h
              apply Exists.elim h
              intro q ex
              apply Exists.elim ex
              intro p h
              have ss : f ⊂ newF := by apply Finset.ssubset_iff_subset_ne.mpr
                                       apply And.intro
                                       · apply Finset.subset_union_right
                                       · intro fe
                                         have := Finset.right_eq_union_iff_subset.mp fe
                                         apply h.2
                                         rw [Finset.biUnion_subset] at this
                                         apply this
                                         exact h.1
              apply Nat.sub_lt_sub_left
              · have : newF ⊆ tn.qs.attach := by simp [· ⊆· ]
                have : tn.qs.attach.card = tn.qs.card := by simp
                rw [←this]
                apply Finset.card_lt_card
                apply Finset.ssubset_of_ssubset_of_subset
                · exact ss
                · assumption
              · simp
                apply Finset.card_lt_card
                exact ss

lemma εclosure_eq_εclosure : εclosure tn f = if h : f = (f.biUnion (fun q => tn.δ q none) ∪ f) then f else εclosure tn (f.biUnion (fun q => tn.δ q none) ∪ f) := by
  apply WellFounded.fixFEq

theorem εclosure_empty_empty : εclosure tn ∅ = ∅ := by
  rw [εclosure_eq_εclosure]
  simp


lemma εclosure_start_mem (q : tn.qs) (f : Finset tn.qs) : q ∈ f → q ∈ εclosure tn f := by
  rw [εclosure_eq_εclosure]
  split
  · simp
  · intro qin
    apply εclosure_start_mem
    apply Finset.mem_union_right
    exact qin

termination_by εclosure_start_mem => tn.qs.card - f.card
decreasing_by have h : ¬f = (Finset.biUnion f fun q => εNFA.δ tn q none) ∪ f := by assumption
              simp at h
              apply Exists.elim h
              intro q ex
              apply Exists.elim ex
              intro p _
              have ss : f ⊂ (Finset.biUnion f fun q => εNFA.δ tn q none) ∪ f := by apply Finset.ssubset_iff_subset_ne.mpr
                                                                                   apply And.intro
                                                                                   · apply Finset.subset_union_right
                                                                                   · assumption
              apply Nat.sub_lt_sub_left
              · have : (Finset.biUnion f fun q => εNFA.δ tn q none) ⊆ tn.qs.attach := by simp [· ⊆· ]
                have : tn.qs.attach.card = tn.qs.card := by simp
                rw [←this]
                apply Finset.card_lt_card
                apply Finset.ssubset_of_ssubset_of_subset
                · exact ss
                · apply Finset.union_subset
                  · assumption
                  · simp [· ⊆ ·]
              · simp
                apply Finset.card_lt_card
                exact ss

@[simp]
def δ_step (q : Finset tn.qs) (e : σs) : Finset tn.qs := (εclosure tn q).biUnion (fun q' => tn.δ q' e)

def δ_star' (q : Finset tn.qs) : (word σs) → Finset tn.qs
  | [] => εclosure tn q
  | a :: as => δ_star' (δ_step tn q a) as

def δ_star (w : word σs) : Finset tn.qs := δ_star' tn tn.q₀ w

def εnfa_accepts (w : word σs) : Prop := (δ_star tn w ∩ tn.fs).Nonempty

instance : Decidable (εnfa_accepts tn w) := by
  simp only [εnfa_accepts]
  apply Finset.decidableNonempty

def εNFA_lang : Lang σs := fun w => εnfa_accepts tn w

instance : Decidable (w ∈ εNFA_lang tn) := by
  apply Finset.decidableNonempty

@[simp]
def εnfa_to_nfa_q : Finset (Finset tn.qs) := tn.qs.attach.powerset

theorem all_in_q (qs : Finset tn.qs) : qs ∈ εnfa_to_nfa_q tn := by
  simp [εnfa_to_nfa_q, · ⊆ ·]

@[simp]
def εnfa_to_nfa_init : { x // x ∈ εnfa_to_nfa_q tn } := ⟨ εclosure tn tn.q₀ , all_in_q tn (εclosure tn tn.q₀)⟩

@[simp]
def εnfa_to_nfa_fs : Finset { x // x ∈ εnfa_to_nfa_q tn } := by
  have fs := (εnfa_to_nfa_q tn).filter (fun q => (q ∩ tn.fs).Nonempty)
  apply fs.biUnion
  intro q
  exact {⟨q , all_in_q tn q⟩}

@[simp]
def εnfa_to_nfa_δ :  { x // x ∈ εnfa_to_nfa_q tn } → σs → Finset { x // x ∈ εnfa_to_nfa_q tn} := by
  intro q e
  have := εclosure tn (q.1.biUnion (fun q => tn.δ q e))
  exact {⟨ this , all_in_q tn this⟩}

@[simp]
def εnfa_to_nfa : NFA σs :=
  {q₀ := {εnfa_to_nfa_init tn}, fs := εnfa_to_nfa_fs tn, δ := εnfa_to_nfa_δ tn}

theorem δ_star'_eq (w : word σs): (q : Finset tn.qs) → {⟨(εNFA.δ_star' tn q w) , all_in_q tn  (εNFA.δ_star' tn q w)⟩} = NFA.δ_star' (εnfa_to_nfa tn) {⟨εclosure tn q , all_in_q tn _⟩} w := by
  induction w with
  | nil => simp [δ_star']
  | cons a as s => intro q
                   simp only [NFA.δ_star',δ_star',s]
                   apply congr
                   · apply congr
                     · rfl
                     · simp
                   · rfl

theorem δ_star_eq (w : word σs) : {⟨εNFA.δ_star tn w , all_in_q tn (εNFA.δ_star tn w)⟩ } = NFA.δ_star (εnfa_to_nfa tn) w := by
  simp only [δ_star]
  rw [δ_star'_eq tn w tn.q₀]
  simp

theorem εnfa_to_nfa_eq (w : word σs) : εnfa_accepts tn w ↔ nfa_accepts (εnfa_to_nfa tn) w := by
  simp only [nfa_accepts,εnfa_accepts]
  apply Iff.intro
  · intro a
    rw [←δ_star_eq]
    apply in_nonempty_inter_singleton
    simp only [δ_star,εnfa_to_nfa,εnfa_to_nfa_fs,Finset.mem_biUnion,Finset.mem_singleton,Finset.mem_filter,Subtype.mk_eq_mk]
    exists δ_star tn w
    apply And.intro
    · exact ⟨by apply all_in_q, a⟩
    · simp [δ_star]
  . intro a
    rw [←δ_star_eq] at a
    have := nonempty_inter_singleton_imp_in ⟨δ_star tn w, all_in_q tn (δ_star tn w)⟩ (εnfa_to_nfa tn).fs
    have := this a
    simp only [δ_star,εnfa_to_nfa,εnfa_to_nfa_fs,Finset.mem_biUnion,Finset.mem_singleton,Finset.mem_filter,Subtype.mk_eq_mk] at this
    apply Exists.elim this
    intro a h
    simp only [δ_star]
    rw [h.2]
    exact h.1.2

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

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

structure εNFA (σs : Finset σ) (qs : Finset q) where
  init : qs        -- initial state
  fs : Finset qs   -- accepting states
  δ : qs → Option σs → Finset qs -- transition function


variable {σ : Type _} {q : Type _} {σs : Finset σ} {qs : Finset q} (r s tn : εNFA σs qs) [DecidableEq σ] [DecidableEq q]


def εclosure (f : Finset qs) : Finset qs := by
  let newF := f.biUnion (fun q => tn.δ q none) ∪ f
  if h : f = newF then exact f else exact εclosure newF

termination_by εclosure => qs.card - f.card
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
              · have : newF ⊆ qs.attach := by simp [· ⊆· ]
                have : qs.attach.card = qs.card := by simp
                rw [←this]
                apply Finset.card_lt_card
                apply Finset.ssubset_of_ssubset_of_subset
                · exact ss
                · assumption
              · simp
                apply Finset.card_lt_card
                exact ss


@[simp]
def δ_step (q : Finset qs) (e : σs) : Finset qs := (εclosure tn q).biUnion (fun q' => tn.δ q' e)

def δ_star' (q : Finset qs) : (word σs) → Finset qs
  | [] => εclosure tn q
  | a :: as => δ_star' (δ_step tn q a) as

def δ_star (w : word σs) : Finset qs := δ_star' tn {tn.init} w

def εnfa_accepts (w : word σs) : Prop := (δ_star tn w ∩ tn.fs).Nonempty

instance : Decidable (εnfa_accepts tn w) := by
  simp only [εnfa_accepts]
  apply Finset.decidableNonempty

@[simp]
def εnfa_to_nfa_q : Finset (Finset qs) := qs.attach.powerset

theorem all_in_q (qs : Finset qs) : qs ∈ εnfa_to_nfa_q := by
  simp [εnfa_to_nfa_q, · ⊆ ·]

@[simp]
def εnfa_to_nfa_init : { x // x ∈ @εnfa_to_nfa_q q qs } := ⟨ εclosure tn {tn.init} , all_in_q (εclosure tn {tn.init})⟩

@[simp]
def εnfa_to_nfa_fs : Finset { x // x ∈ @εnfa_to_nfa_q q qs } := by
  have fs := εnfa_to_nfa_q.filter (fun q => (q ∩ tn.fs).Nonempty)
  apply fs.biUnion
  intro q
  exact {⟨q , all_in_q q⟩}

@[simp]
def εnfa_to_nfa_δ :  { x // x ∈ @εnfa_to_nfa_q q qs } → σs → Finset { x // x ∈ @εnfa_to_nfa_q q qs } := by
  intro q e
  have := εclosure tn (q.1.biUnion (fun q => tn.δ q e))
  exact {⟨ this , all_in_q this⟩}

@[simp]
def εnfa_to_nfa : NFA σs (@εnfa_to_nfa_q q qs) :=
  {init := εnfa_to_nfa_init tn, fs := εnfa_to_nfa_fs tn, δ := εnfa_to_nfa_δ tn}

theorem δ_star'_eq (w : word σs): (q : Finset qs) → {⟨(εNFA.δ_star' tn q w) , all_in_q  (εNFA.δ_star' tn q w)⟩} = NFA.δ_star' (εnfa_to_nfa tn) {⟨εclosure tn q , all_in_q _⟩} w := by
  induction w with
  | nil => simp [δ_star']
  | cons a as s => intro q
                   simp [NFA.δ_star',δ_star',s]

theorem δ_star_eq (w : word σs) : {⟨εNFA.δ_star tn w , all_in_q  (εNFA.δ_star tn w)⟩ } = NFA.δ_star (εnfa_to_nfa tn) w := by
  simp only [δ_star]
  rw [δ_star'_eq tn w {tn.init}]
  simp

theorem εnfa_to_nfa_eq (w : word σs) : εnfa_accepts tn w ↔ nfa_accepts (εnfa_to_nfa tn) w := by
  simp only [nfa_accepts,εnfa_accepts]
  apply Iff.intro
  · intro a
    rw [←δ_star_eq]
    apply in_nonempty_inter_singleton
    simp only [δ_star,εnfa_to_nfa,εnfa_to_nfa_fs,Finset.mem_biUnion,Finset.mem_singleton,Finset.mem_filter]
    exists δ_star tn w
    apply And.intro
    · exact ⟨by simp [εnfa_to_nfa_q,δ_star,· ⊆ ·], a⟩
    · simp [δ_star]
  . intro a
    rw [←δ_star_eq] at a
    have := nonempty_inter_singleton_imp_in ⟨δ_star tn w, all_in_q (δ_star tn w)⟩ (εnfa_to_nfa tn).fs
    have := this a
    simp only [δ_star,εnfa_to_nfa,εnfa_to_nfa_fs,Finset.mem_biUnion,Finset.mem_singleton,Finset.mem_filter] at this
    apply Exists.elim this
    intro a h
    have := h.1.2
    rw [Subtype.mk_eq_mk] at h
    rw [←h.2] at this
    exact this

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

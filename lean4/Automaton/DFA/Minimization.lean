import Automaton.DFA.Basic
import Automaton.Finset.Basic
import Mathlib.Data.FinEnum
import Mathlib.Data.List.Basic

open DFA Finset

namespace DFA

variable {σ : Type _} {q : Type _} {r s t : DFA σ q} [DecidableEq σ] [DecidableEq q]

@[simp]
def minimization_reachable_q (t : DFA σ q) : Finset t.qs := t.qs.attach.filter (fun q => reachable t t.init q)

@[simp]
def minimization_reachable_init (t : DFA σ q) : { x // x ∈ minimization_reachable_q t } := by
  exact ⟨t.init , by simp [finenum_to_finset]; exact reachable.base⟩

@[simp]
def minimization_reachable_fs (t : DFA σ q) : Finset {x // x ∈ minimization_reachable_q t} := by
  have := Finset.attach (minimization_reachable_q t)
  exact this.filter (fun q => q.1 ∈ t.fs)

@[simp]
def minimization_reachable_δ (t : DFA σ q) : { x // x ∈ minimization_reachable_q t } → t.σs → { x // x ∈ minimization_reachable_q t } := by
  intro q e
  have := q.2
  simp [finenum_to_finset] at this
  exact ⟨ t.δ q e, by simp [finenum_to_finset]; apply reachable.step; exact this⟩

def minimization_reachable (t : DFA σ q) : DFA σ {x // x ∈ t.qs} :=
  {qs := minimization_reachable_q t, init := minimization_reachable_init t, fs := minimization_reachable_fs t, δ := minimization_reachable_δ t}

lemma minimization_reachable_δ_star'_eq (w : word t.σs) : (q : t.qs) → (r : reachable t t.init q) → δ_star' t q w = (δ_star' (minimization_reachable t) ⟨q, by simp [finenum_to_finset, minimization_reachable]; exact r⟩  w).1 := by
  induction w with
  | nil => simp
  | cons a as s => simp only [δ_star']
                   intro q r
                   rw [s]
                   simp [minimization_reachable]
                   apply reachable.step
                   exact r

theorem minimization_reachable_δ_star_eq (w : word t.σs) : δ_star t w = (δ_star (minimization_reachable t) w).1 := by
  simp only [δ_star]
  apply minimization_reachable_δ_star'_eq
  exact reachable.base

theorem minimization_reachable_eq {w : word t.σs} : dfa_accepts t w ↔ dfa_accepts (minimization_reachable t) w := by
  apply Iff.intro
  · intro dfa
    simp only [dfa_accepts] at dfa
    simp only [dfa_accepts]
    simp [minimization_reachable]
    rw [minimization_reachable_δ_star_eq] at dfa
    simp [minimization_reachable] at dfa
    exact dfa
  · intro dfa
    simp only [dfa_accepts] at dfa
    simp only [dfa_accepts]
    rw [minimization_reachable_δ_star_eq]
    simp [minimization_reachable] at dfa
    simp [minimization_reachable]
    exact dfa

inductive distinct : t.qs → t.qs → Prop where
  | base (a b : t.qs) : ¬(a ∈ t.fs ↔ b ∈ t.fs) → distinct a b
  | step (a b : t.qs) : ∀ s : t.σs, distinct (t.δ a s) (t.δ b s) → distinct a b

def nondistinct (a b : t.qs) : Prop := ¬ distinct a b

lemma distinct_if_δ_star'_distinct (w : word t.σs) : (a b : t.qs) → distinct (δ_star' t a w) (δ_star' t b w) → distinct a b := by
  induction w using List.reverseRecOn  with
  | H0 => intro a b d
          simp at d
          exact d
  | H1 a b s => intro a b d
                rw [←δ_δ_star'_concat_eq_δ_star',←δ_δ_star'_concat_eq_δ_star'] at d
                apply s
                apply distinct.step
                exact d


theorem distinct_iff_ex_notaccepted (a b : t.qs) : distinct a b ↔ ∃ l : word t.σs, ¬(δ_star' t a l ∈ t.fs ↔ δ_star' t b l ∈ t.fs) := by
  apply Iff.intro
  · intro d
    induction d with
    | base a b h => exists []
    | step a b g _ s => apply Exists.elim s
                        intro c ex
                        exists (g::c)
  · intro ex
    apply Exists.elim ex
    intro c ex
    have : distinct (δ_star' t a c) (δ_star' t b c) := by apply distinct.base
                                                          exact ex
    apply distinct_if_δ_star'_distinct
    exact this

lemma nondistinct_iff_nex_notaccepted : nondistinct a b ↔ ¬∃ w : word t.σs, ¬(δ_star' t a w ∈ t.fs ↔ δ_star' t b w ∈ t.fs) := by
  simp only [nondistinct]
  apply not_congr
  apply distinct_iff_ex_notaccepted

theorem nondistinct_iff_forall_accepted : nondistinct a b ↔ ∀ w : word t.σs, (δ_star' t a w ∈ t.fs ↔ δ_star' t b w ∈ t.fs) := by
  rw [←Decidable.not_exists_not]
  apply nondistinct_iff_nex_notaccepted


theorem nondistinct.Symm {a b: t.qs} : nondistinct a b → nondistinct b a := by
  intro n
  simp only [nondistinct]
  simp only [nondistinct] at n
  intro d
  apply n
  induction d with
  | base a b h => apply distinct.base
                  apply Decidable.not_iff.mpr
                  apply Decidable.not_iff_comm.mp
                  apply Decidable.not_iff.mp
                  exact h
  | step c d s _ h => apply distinct.step
                      apply h
                      intro d
                      apply n
                      apply distinct.step
                      exact d

theorem nondistinct.Refl {a : t.qs} : nondistinct a a := by
  intro d
  rw [distinct_iff_ex_notaccepted] at d
  apply Exists.elim d
  intro w h
  apply h
  rfl

theorem nondistinct.Trans {a b c : t.qs} : nondistinct a b → nondistinct b c → nondistinct a c := by
  intro n₁ n₂
  rw [nondistinct_iff_forall_accepted] at n₁
  rw [nondistinct_iff_forall_accepted] at n₂
  rw [nondistinct_iff_forall_accepted]
  intro w
  apply Iff.intro
  · intro ain
    apply (n₂ w).mp
    apply (n₁ w).mp
    exact ain
  · intro cin
    apply (n₁ w).mpr
    apply (n₂ w).mpr
    exact cin

theorem nondistinct_step {a b : t.qs} {e : t.σs} : nondistinct a b → nondistinct (t.δ a e) (t.δ b e) := by
  intro n
  intro d
  apply n
  apply distinct.step
  exact d

theorem nondistinct_self {a : t.qs} : nondistinct a a := by
  simp only [nondistinct]
  intro d
  rw [distinct_iff_ex_notaccepted] at d
  apply Exists.elim d
  intro l h
  apply h
  trivial

instance instNondistinctEquivalence : Equivalence (@nondistinct σ q t) := by
  apply Equivalence.mk
  · intro a; exact nondistinct.Refl
  · exact nondistinct.Symm
  · exact nondistinct.Trans

-- Table filling algorithm

def all_pairs (t : DFA σ q) : Finset (t.qs × t.qs) := t.qs.attach.biUnion (fun q₁ => t.qs.attach.biUnion (fun q₂ => {⟨q₁,q₂⟩}))

def start : Finset (t.qs × t.qs) := (all_pairs t).filter (fun (a,b) => ¬(a ∈ t.fs ↔ b ∈ t.fs))

lemma start_subset_all : start  ⊆ all_pairs t := by
  simp [start]

def step (c a : Finset (t.qs × t.qs)) : Finset (t.qs × t.qs) := c ∪ (a.filter (fun (a,b) => ∃ s : t.σs, (t.δ a s, t.δ b s) ∈ c))

theorem table_aux_decreasing : ¬card (step c (all_pairs t)) = card c → c ⊆ all_pairs t → (all_pairs t).card - (step c (all_pairs t)).card < (all_pairs t).card - c.card := by
  intro g h
  have h₁ : (step c (all_pairs t)).card >= c.card := by simp only [step]
                                                        apply Finset.card_le_of_subset
                                                        apply Finset.subset_union_left
  have h₂ : card c < card (step c (all_pairs t)) := by apply Nat.lt_iff_le_and_ne.mpr
                                                       apply And.intro
                                                       · exact h₁
                                                       · simp at g
                                                         intro eq
                                                         apply g
                                                         simp at eq
                                                         apply Eq.symm
                                                         exact eq
  have s : step c (all_pairs t) ⊆ (all_pairs t) := by simp only [step]
                                                      apply Finset.union_subset
                                                      · exact h
                                                      · apply Finset.filter_subset
  have d : c ⊂ step c (all_pairs t) := by apply Finset.ssubset_iff_subset_ne.mpr
                                          apply And.intro
                                          · simp only [step]
                                            apply Finset.subset_union_left
                                          · intro eq
                                            apply g
                                            rw [←eq]
  have : (all_pairs t).card - (step c (all_pairs t)).card < (all_pairs t).card - c.card := by apply Nat.sub_lt_sub_left
                                                                                              · apply Nat.lt_iff_le_and_ne.mpr
                                                                                                apply And.intro
                                                                                                · apply Finset.card_le_of_subset
                                                                                                  exact h
                                                                                                · apply Nat.ne_of_lt
                                                                                                  apply Finset.card_lt_card
                                                                                                  apply Finset.ssubset_of_ssubset_of_subset
                                                                                                  · exact d
                                                                                                  · exact s
                                                                                              · exact h₂
  exact this

def table_aux (c : Finset (t.qs × t.qs)) (h : c ⊆ (all_pairs t)) : Finset (t.qs × t.qs) := by
  let a := all_pairs t
  if (step c a).card = c.card then exact c else exact table_aux (step c a) (by simp only [step]
                                                                               apply Finset.union_subset_iff.mpr
                                                                               apply And.intro
                                                                               · exact h
                                                                               · simp)
termination_by table_aux c h => (all_pairs t).card - c.card
decreasing_by have : (all_pairs t).card - (step c (all_pairs t)).card < (all_pairs t).card - c.card := by apply table_aux_decreasing (by assumption) (by assumption)
              apply this

def table_filling : Finset (t.qs × t.qs) := table_aux start start_subset_all

def distinct_table_filling (a b : t.qs) : Bool := ⟨a,b⟩ ∈ table_filling

lemma step_subset (a b : Finset ({ x // x ∈ t.qs } × { x // x ∈ t.qs })) : a ⊆ b → step a b ⊆ b := by
  intro ss
  simp only [step]
  apply Finset.union_subset_iff.mpr
  apply And.intro
  · exact ss
  · simp

lemma table_aux_eq_table_aux : table_aux c h = if (step c (all_pairs t)).card = c.card then c else table_aux (step c (all_pairs t)) (step_subset c (all_pairs t) h) := by
  apply WellFounded.fixFEq

theorem table_aux_forall (P : Finset (t.qs × t.qs) → Prop) (c : Finset (t.qs × t.qs)) {h : c ⊆ all_pairs t} : P c → (∀ f : Finset (t.qs × t.qs), P f → P (step f (all_pairs t))) → P (table_aux c h) := by
  intro b fa
  rw [table_aux_eq_table_aux]
  split
  · exact b
  · apply table_aux_forall
    · apply fa
      exact b
    · apply fa
termination_by table_aux_forall p => (all_pairs t).card - c.card
decreasing_by have : (all_pairs t).card - (step c (all_pairs t)).card < (all_pairs t).card - c.card := by apply table_aux_decreasing (by assumption) (by assumption)
              apply this

def ex_word_prop : Finset (t.qs × t.qs) → Prop := fun f => ∀ p : (t.qs × t.qs), p ∈ f → ∃ w : word t.σs, ¬(δ_star' t p.1 w ∈ t.fs ↔ δ_star' t p.2 w ∈ t.fs)

lemma exists_notaccepted_if_table_filling (t : DFA σ q) : ex_word_prop (table_aux start (@start_subset_all σ q t _)) := by
  apply table_aux_forall
  · simp [ex_word_prop,start]
    intro a b c d _ nin
    exists []
  · intro f p
    simp [ex_word_prop] at p
    simp [ex_word_prop,step]
    intro a p₁ b p₂ h
    cases h with
    | inl h => apply p; exact h
    | inr h => apply Exists.elim h.2
               intro s h₁
               apply Exists.elim h₁
               intro p₃ e
               have := p (t.δ ⟨a, p₁⟩ ⟨s , p₃⟩) (by simp) (t.δ ⟨b, p₂⟩ ⟨s , p₃⟩) (by simp) e
               apply Exists.elim this
               intro w h
               rw [←distinct_iff_ex_notaccepted]
               rw [←distinct_iff_ex_notaccepted] at this
               apply distinct.step
               exact this

lemma step_gt_if (c : Finset _)(a b : t.qs) (e : t.σs): ⟨t.δ a e, t.δ b e⟩ ∈ c → ⟨a,b⟩ ∉ c → (step c (all_pairs t)).card > c.card := by
  intro inc ninc
  simp only [step]
  apply Finset.card_lt_card
  have : c ⊆ c ∪ filter (fun x => ∃ s, (DFA.δ t x.fst s, DFA.δ t x.snd s) ∈ c) (all_pairs t) := by apply Finset.subset_union_left
  have := Finset.ssubset_iff_of_subset this
  apply this.mpr
  exists ⟨a,b⟩
  · apply And.intro
    · apply Finset.mem_union_right
      simp only [Finset.mem_filter]
      apply And.intro
      · simp [all_pairs]
      · exists e
    · exact ninc

lemma if_δ_in_table_aux_in_table_aux : ⟨t.δ a e, t.δ b e⟩ ∈ table_aux c h → ⟨a,b⟩ ∈ table_aux c h := by
  intro δ
  rw [table_aux_eq_table_aux]
  rw [table_aux_eq_table_aux] at δ
  split
  · split at δ
    · cases (Decidable.em (⟨a,b⟩ ∈ c)) with
      | inl h => exact h
      | inr h => have := step_gt_if c a b e δ h
                 have : card (step c (all_pairs t)) ≠ card c := by apply Nat.ne_of_gt
                                                                   exact this
                 contradiction
    · contradiction
  · split at δ
    · contradiction
    · apply if_δ_in_table_aux_in_table_aux
      · exact δ
termination_by if_δ_in_table_aux_in_table_aux p => (all_pairs t).card - c.card
decreasing_by have : (all_pairs t).card - (step c (all_pairs t)).card < (all_pairs t).card - c.card := by apply table_aux_decreasing (by assumption) (by assumption)
              apply this


lemma table_filling_if_exists (w : word t.σs): (a b : t.qs) → ¬(δ_star' t a w ∈ t.fs ↔ δ_star' t b w ∈ t.fs) → distinct_table_filling a b := by
  simp only [distinct_table_filling,table_filling]
  induction w  with
  | nil => intro a b h
           simp only [δ_star'] at h
           rw [decide_eq_true_eq]
           apply table_aux_forall
           · simp only [start]
             rw [Finset.mem_filter]
             apply And.intro
             · simp [all_pairs]
             · exact h
           · intro f inf
             simp only [step]
             apply Finset.mem_union.mpr
             apply Or.inl
             exact inf
    | cons e es s => intro a b h
                     rw [decide_eq_true_eq]
                     simp only [δ_star] at h
                     have δ := s (t.δ a e) (t.δ b e) h
                     rw [decide_eq_true_eq] at δ
                     apply if_δ_in_table_aux_in_table_aux
                     exact δ

theorem forall_step_exists_word (a b : t.qs) : distinct_table_filling a b ↔ ∃ w : word t.σs, ¬(δ_star' t a w ∈ t.fs ↔ δ_star' t b w ∈ t.fs) := by
  apply Iff.intro
  · intro d
    simp only [distinct_table_filling] at d
    rw [decide_eq_true_eq] at d
    have := exists_notaccepted_if_table_filling t
    simp only [ex_word_prop] at this
    have := this ⟨a,b⟩
    apply this
    exact d
  · intro ex
    apply Exists.elim ex
    intro w h
    apply table_filling_if_exists
    . exact h

instance instDecExW : Decidable (∃ w : word t.σs, ¬(δ_star' t a w ∈ t.fs ↔ δ_star' t b w ∈ t.fs)) := by
  apply decidable_of_iff (distinct_table_filling a b)
  exact forall_step_exists_word a b

instance instDecDistinct : Decidable (@distinct σ q t a b) := by
  apply decidable_of_iff (∃ w : word t.σs, ¬(δ_star' t a w ∈ t.fs ↔ δ_star' t b w ∈ t.fs))
  apply Iff.symm
  apply distinct_iff_ex_notaccepted

instance instDecNondistinct : Decidable (@nondistinct σ q t a b) := by
  simp only [nondistinct]
  infer_instance

-- Minimization of DFA using nondistinct states

def min_q (t : DFA σ q) : Finset (Finset t.qs) := t.qs.attach.biUnion (fun q => {t.qs.attach.filter (fun q' => nondistinct q' q)})

def min_init (t : DFA σ q) : { x // x ∈ min_q t } := by
  simp only [min_q]
  exact ⟨t.qs.attach.filter (fun q => nondistinct q t.init), by rw [Finset.mem_biUnion]; exists t.init; rw [Finset.mem_singleton]; exact ⟨by simp, rfl⟩⟩

def min_fs (t : DFA σ q) : Finset { x // x ∈ min_q t } := (min_q t).attach.filter (fun f => ∃ q : t.qs, q ∈ f.1 ∧ q ∈ t.fs)

theorem min_δ_step_in (a : { x // x ∈ min_q t }) : a.1.biUnion (fun a => (t.qs.attach).filter (fun b => nondistinct b (t.δ a e))) ∈ min_q t := by
  simp only [min_q]
  simp only [min_q] at a
  have := a.2
  rw [Finset.mem_biUnion] at this
  apply Exists.elim this
  intro q ex
  rw [Finset.mem_singleton] at ex
  rw [Finset.mem_biUnion]
  exists (t.δ q e)
  exists (by simp)
  rw [Finset.mem_singleton]
  apply mem_iff_mem_eq
  intro el
  rw [ex.2]
  rw [Finset.mem_biUnion,Finset.mem_filter]
  apply Iff.intro
  · intro elin
    apply Exists.elim elin
    intro q₁ h
    rw [Finset.mem_filter,Finset.mem_filter] at h
    have : nondistinct (t.δ q₁ e) (t.δ q e) := nondistinct_step h.1.2
    apply And.intro
    · simp
    · apply nondistinct.Trans
      exact h.2.2
      exact this
  · intro elin
    exists q
    rw [Finset.mem_filter,Finset.mem_filter]
    apply And.intro
    · exact ⟨by simp, by apply nondistinct_self⟩
    · exact ⟨by simp, by exact elin.2⟩

def min_δ : { x // x ∈ min_q t } → { x // x ∈ t.σs } → { x // x ∈ min_q t } := by
  intro a e
  let b := a.1.biUnion (fun a => (t.qs.attach).filter (fun b => nondistinct b (t.δ a e)))
  exact ⟨b , min_δ_step_in a⟩

def min_dfa (t : DFA σ q) : DFA σ (Finset t.qs) := {qs := min_q t, σs := t.σs, init := min_init t, fs := min_fs t, δ := min_δ}

def state_eq_class (a : t.qs) : { x // x ∈ (min_dfa t).qs } := ⟨t.qs.attach.filter (fun q => nondistinct q a), by simp [min_dfa,min_q]; exists a; exists (by simp)⟩

lemma step_eq_class_eq : state_eq_class (DFA.δ t a e) = DFA.δ (min_dfa t) (state_eq_class a) e := by
  simp only [state_eq_class,min_dfa,min_δ]
  rw [Subtype.mk_eq_mk]
  apply mem_iff_mem_eq
  intro q
  apply Iff.intro
  · intro ein
    rw [Finset.mem_filter] at ein
    rw [Finset.mem_biUnion]
    exists a
    rw [Finset.mem_filter,Finset.mem_filter]
    apply And.intro
    · exact ⟨by simp, nondistinct_self⟩
    · exact ein
  · intro ein
    rw [Finset.mem_biUnion] at ein
    apply Exists.elim ein
    intro a₁ ex₁
    rw [Finset.mem_filter,Finset.mem_filter] at ex₁
    rw [Finset.mem_filter]
    apply And.intro
    · simp
    · apply nondistinct.Trans
      · exact ex₁.2.2
      apply nondistinct_step
      exact ex₁.1.2

theorem min_δ'_accepts_iff {w : word t.σs} : {a : t.qs} → (δ_star' t a w ∈ t.fs ↔ δ_star' (min_dfa t) (state_eq_class a) w ∈ (min_dfa t).fs) := by
  induction w with
  | nil => intro a
           simp only [δ_star',state_eq_class,min_dfa]
           apply Iff.intro
           · intro ain
             simp only [min_fs]
             rw [Finset.mem_filter]
             apply And.intro
             · simp only [min_q]
               apply Finset.mem_attach
             · exists a
               rw [Finset.mem_filter]
               apply And.intro
               · exact ⟨by simp, nondistinct_self⟩
               · exact ain
           · intro h
             simp only [min_fs] at h
             rw [Finset.mem_filter] at h
             apply Exists.elim h.2
             intro q h
             rw [Finset.mem_filter] at h
             have := nondistinct_iff_forall_accepted.mp h.1.2 []
             simp only [δ_star'] at this
             apply this.mp
             exact h.2
  | cons e es s => intro a
                   simp only [δ_star']
                   have eq : state_eq_class (DFA.δ t a e) = DFA.δ (min_dfa t) (state_eq_class a) e := by apply step_eq_class_eq
                   apply Iff.intro
                   · intro din
                     have s := s.mp din
                     rw [←eq]
                     exact s
                   · intro sin
                     rw [←eq] at sin
                     have s := s.mpr sin
                     exact s

theorem min_eq {w : word t.σs} : dfa_accepts t w ↔ dfa_accepts (min_dfa t) w := by
  simp only [dfa_accepts,δ_star]
  apply min_δ'_accepts_iff

theorem min_reachable_min_eq {w : word t.σs} : dfa_accepts (minimization_reachable t) w ↔ dfa_accepts (min_dfa (minimization_reachable t)) w := by
  apply min_eq

theorem min_min_eq {w : word t.σs} : dfa_accepts t w ↔ dfa_accepts (min_dfa (minimization_reachable t)) w := by
  apply Iff.intro
  · intro d
    apply min_reachable_min_eq.mp
    apply minimization_reachable_eq.mp
    exact d
  · intro d
    apply minimization_reachable_eq.mpr
    apply min_reachable_min_eq.mpr
    exact d

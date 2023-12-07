import Automaton.DFA.Basic
import Automaton.Finset.Basic
import Mathlib.Data.FinEnum
import Mathlib.Data.List.Basic

open DFA Finset

namespace DFA

variable {σ : Type _} {q : Type _}  {σs : Finset σ} {qs : Finset q} [DecidableEq σ] [DecidableEq q] (r s t : DFA σs qs)

@[simp]
def minimization_reachable_q (t : DFA σs qs) : Finset qs := qs.attach.filter (fun q => reachable t t.s q)

@[simp]
def minimization_reachable_init (t : DFA σs qs) : { x // x ∈ minimization_reachable_q t } := by
  exact ⟨t.s , by simp [finenum_to_finset]; exact reachable.base⟩

@[simp]
def minimization_reachable_fs (t : DFA σs qs) : Finset {x // x ∈ minimization_reachable_q t} := by
  have := Finset.attach (minimization_reachable_q t)
  exact this.filter (fun q => q.1 ∈ t.fs)

@[simp]
def minimization_reachable_δ (t : DFA σs qs) : { x // x ∈ minimization_reachable_q t } → σs → { x // x ∈ minimization_reachable_q t } := by
  intro q e
  have := q.2
  simp [finenum_to_finset] at this
  exact ⟨ t.δ q e, by simp [finenum_to_finset]; apply reachable.step; exact this⟩

def minimization_reachable (t : DFA σs qs) : DFA σs (minimization_reachable_q t) :=
  {s := minimization_reachable_init t, fs := minimization_reachable_fs t, δ := minimization_reachable_δ t}

lemma minimization_reachable_δ_star'_eq (w : word σs) : (q : qs) → (r : reachable t t.s q) → δ_star' t q w = (δ_star' (minimization_reachable t) ⟨q, by simp [finenum_to_finset, minimization_reachable]; exact r⟩  w).1 := by
  induction w with
  | nil => simp
  | cons a as s => simp only [δ_star']
                   intro q r
                   rw [s]
                   simp [minimization_reachable]
                   apply reachable.step
                   exact r

theorem minimization_reachable_δ_star_eq (w : word σs) : δ_star t w = (δ_star (minimization_reachable t) w).1 := by
  simp only [δ_star]
  apply minimization_reachable_δ_star'_eq
  exact reachable.base

theorem minimization_reachable_eq {w : word σs} : dfa_accepts t w ↔ dfa_accepts (minimization_reachable t) w := by
  apply Iff.intro
  · intro dfa
    simp only [dfa_accepts] at dfa
    simp only [dfa_accepts]
    rw [minimization_reachable_δ_star_eq] at dfa
    simp [minimization_reachable] at dfa
    simp [minimization_reachable]
    apply Finset.mem_filter.mpr
    apply And.intro
    · simp
    · exact dfa
  · intro dfa
    simp only [dfa_accepts] at dfa
    simp only [dfa_accepts]
    rw [minimization_reachable_δ_star_eq]
    simp [minimization_reachable] at dfa
    simp [minimization_reachable]
    have := Finset.mem_filter.mp dfa
    exact this.2


inductive distinct : qs → qs → Prop where
  | base (a b : qs) : ¬(a ∈ t.fs ↔ b ∈ t.fs) → distinct a b
  | step (a b : qs) : ∀ s : σs, distinct (t.δ a s) (t.δ b s) → distinct a b

def nondistinct (a b : qs) : Prop := ¬ distinct t a b

lemma distinct_if_δ_star'_distinct (w : word σs) : (a b : qs) → distinct t (δ_star' t a w) (δ_star' t b w) → distinct t a b := by
  induction w using List.reverseRecOn  with
  | H0 => intro a b d
          simp only [δ_star'] at d
          exact d
  | H1 a b s => intro a b d
                rw [←δ_δ_star'_concat_eq_δ_star',←δ_δ_star'_concat_eq_δ_star'] at d
                apply s
                apply distinct.step
                exact d


theorem distinct_iff_ex_notaccepted (a b : qs) : distinct t a b ↔ ∃ l : word σs, ¬(δ_star' t a l ∈ t.fs ↔ δ_star' t b l ∈ t.fs) := by
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
    have : distinct t (δ_star' t a c) (δ_star' t b c) := by apply distinct.base
                                                            exact ex
    apply distinct_if_δ_star'_distinct
    exact this

lemma nondistinct_iff_nex_notaccepted : nondistinct t a b ↔ ¬∃ w : word σs, ¬(δ_star' t a w ∈ t.fs ↔ δ_star' t b w ∈ t.fs) := by
  simp only [nondistinct]
  apply not_congr
  apply distinct_iff_ex_notaccepted

theorem nondistinct_iff_forall_accepted : nondistinct t a b ↔ ∀ w : word σs, (δ_star' t a w ∈ t.fs ↔ δ_star' t b w ∈ t.fs) := by
  rw [←Decidable.not_exists_not]
  apply nondistinct_iff_nex_notaccepted

theorem nondistinct.Symm {a b: qs} : nondistinct t a b → nondistinct t b a := by
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

theorem nondistinct.Refl {a : qs} : nondistinct t a a := by
  intro d
  rw [distinct_iff_ex_notaccepted] at d
  apply Exists.elim d
  intro w h
  apply h
  rfl

theorem nondistinct.Trans {a b c : qs} : nondistinct t a b → nondistinct t b c → nondistinct t a c := by
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

theorem nondistinct_step {a b : qs} {e : σs} : nondistinct t a b → nondistinct t (t.δ a e) (t.δ b e) := by
  intro n
  intro d
  apply n
  apply distinct.step
  exact d

theorem nondistinct_self {a : qs} : nondistinct t a a := by
  simp only [nondistinct]
  intro d
  rw [distinct_iff_ex_notaccepted] at d
  apply Exists.elim d
  intro l h
  apply h
  apply (iff_self_iff _).mpr
  constructor

instance instNondistinctEquivalence : Equivalence (nondistinct t) := by
  apply Equivalence.mk
  · intro a; exact nondistinct.Refl t
  · exact nondistinct.Symm t
  · exact nondistinct.Trans t

-- Table filling algorithm

def all_pairs : Finset (qs × qs) := qs.attach.biUnion (fun q₁ => qs.attach.biUnion (fun q₂ => {⟨q₁,q₂⟩}))

def start : Finset (qs × qs) := all_pairs.filter (fun (a,b) => ¬(a ∈ t.fs ↔ b ∈ t.fs))

lemma start_subset_all : start t  ⊆ all_pairs := by
  simp [start]

def step (c a : Finset (qs × qs)) : Finset (qs × qs) := c ∪ (a.filter (fun (a,b) => ∃ s : σs, (t.δ a s, t.δ b s) ∈ c))

lemma table_aux_decreasing : ¬card (step t c all_pairs) = card c → c ⊆ all_pairs → (@all_pairs q qs).card - (step t c all_pairs).card < (@all_pairs q qs).card - c.card := by
  intro g h
  have d : c ⊂ step t c   all_pairs := by apply Finset.ssubset_iff_subset_ne.mpr
                                          apply And.intro
                                          · simp only [step]
                                            apply Finset.subset_union_left
                                          · intro eq
                                            apply g
                                            rw [←eq]
  apply Nat.sub_lt_sub_left
  · apply Nat.lt_iff_le_and_ne.mpr
    apply And.intro
    · apply Finset.card_le_of_subset
      exact h
    · apply Nat.ne_of_lt
      apply Finset.card_lt_card
      apply Finset.ssubset_of_ssubset_of_subset
      · exact d
      · simp only [step]
        apply Finset.union_subset
        · exact h
        · apply Finset.filter_subset
  · apply Finset.card_lt_card
    exact d

def table_aux (c : Finset (qs × qs)) (h : c ⊆ all_pairs) : Finset (qs × qs) := by
  if (step t c all_pairs).card = c.card then exact c else exact table_aux (step t c all_pairs) (by simp only [step]
                                                                                                   apply Finset.union_subset_iff.mpr
                                                                                                   apply And.intro
                                                                                                   · exact h
                                                                                                   · simp)
termination_by table_aux c h => (@all_pairs q qs).card - c.card
decreasing_by apply table_aux_decreasing t (by assumption) (by assumption)

def table_filling : Finset (qs × qs) := table_aux t (start t) (start_subset_all t)

def distinct_table_filling (a b : qs) : Bool := ⟨a,b⟩ ∈ table_filling t

lemma step_subset (a b : Finset ({ x // x ∈ qs } × { x // x ∈ qs })) : a ⊆ b → step t a b ⊆ b := by
  intro ss
  simp only [step]
  apply Finset.union_subset_iff.mpr
  apply And.intro
  · exact ss
  · apply Finset.filter_subset

lemma table_aux_eq_table_aux : table_aux t c h = if (step t c all_pairs).card = c.card then c else table_aux t (step t c all_pairs) (step_subset t c all_pairs h) := by
  apply WellFounded.fixFEq

theorem table_aux_forall (P : Finset (qs × qs) → Prop) (c : Finset (qs × qs)) {h : c ⊆ all_pairs} : P c → (∀ f : Finset (qs × qs), P f → P (step t f all_pairs)) → P (table_aux t c h) := by
  intro b fa
  rw [table_aux_eq_table_aux]
  split
  · exact b
  · apply table_aux_forall
    · apply fa
      exact b
    · apply fa
termination_by table_aux_forall p => (@all_pairs q qs).card - c.card
decreasing_by apply table_aux_decreasing t (by assumption) (by assumption)

def ex_word_prop : Finset (qs × qs) → Prop := fun f => ∀ p : (qs × qs), p ∈ f → ∃ w : word σs, ¬(δ_star' t p.1 w ∈ t.fs ↔ δ_star' t p.2 w ∈ t.fs)

lemma exists_notaccepted_if_table_filling  : ex_word_prop t (table_aux t (start t) (start_subset_all t)) := by
  apply table_aux_forall
  · simp only [ex_word_prop,start]
    intro a
    rw [Finset.mem_filter]
    intro b
    exists []
    simp only [δ_star']
    exact b.2
  · intro f p
    simp only [ex_word_prop] at p
    simp only [ex_word_prop,step]
    intro a p
    rw [Finset.mem_union] at p
    cases p with
    | inl h => apply p; exact h
    | inr h => rw [Finset.mem_filter] at h
               apply Exists.elim h.2
               intro s h₁
               rw [←distinct_iff_ex_notaccepted]
               have := p (DFA.δ t a.fst s, DFA.δ t a.snd s) h₁
               rw [←distinct_iff_ex_notaccepted] at this
               apply distinct.step
               exact this

lemma step_gt_if (c : Finset _)(a b : qs) (e : σs) : ⟨t.δ a e, t.δ b e⟩ ∈ c → ⟨a,b⟩ ∉ c → (step t c all_pairs).card > c.card := by
  intro inc ninc
  simp only [step]
  apply Finset.card_lt_card
  have : c ⊆ c ∪ filter (fun x => ∃ s, (DFA.δ t x.fst s, DFA.δ t x.snd s) ∈ c) all_pairs := by apply Finset.subset_union_left
  apply (Finset.ssubset_iff_of_subset this).mpr
  exists ⟨a,b⟩
  apply And.intro
  · apply Finset.mem_union_right
    simp only [Finset.mem_filter]
    apply And.intro
    · simp [all_pairs]
    · exists e
  · exact ninc

lemma if_δ_in_table_aux_in_table_aux : ⟨t.δ a e, t.δ b e⟩ ∈ table_aux t c h → ⟨a,b⟩ ∈ table_aux t c h := by
  intro δ
  rw [table_aux_eq_table_aux]
  rw [table_aux_eq_table_aux] at δ
  split
  · split at δ
    · cases (Decidable.em (⟨a,b⟩ ∈ c)) with
      | inl h => exact h
      | inr h => have := step_gt_if t c a b e δ h
                 have : card (step t c all_pairs) ≠ card c := by apply Nat.ne_of_gt
                                                                 exact this
                 contradiction
    · contradiction
  · split at δ
    · contradiction
    · apply if_δ_in_table_aux_in_table_aux
      · exact δ
termination_by if_δ_in_table_aux_in_table_aux p => (@all_pairs q qs).card - c.card
decreasing_by apply table_aux_decreasing t (by assumption) (by assumption)


lemma table_filling_if_exists (w : word σs) : (a b : qs) → ¬(δ_star' t a w ∈ t.fs ↔ δ_star' t b w ∈ t.fs) → distinct_table_filling t a b := by
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
                     have δ := s (t.δ a e) (t.δ b e) h
                     rw [decide_eq_true_eq] at δ
                     apply if_δ_in_table_aux_in_table_aux
                     exact δ

theorem forall_step_exists_word (a b : qs) : distinct_table_filling t a b ↔ ∃ w : word σs, ¬(δ_star' t a w ∈ t.fs ↔ δ_star' t b w ∈ t.fs) := by
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

instance instDecExW : Decidable (∃ w : word σs, ¬(δ_star' t a w ∈ t.fs ↔ δ_star' t b w ∈ t.fs)) := by
  apply decidable_of_iff (distinct_table_filling t a b)
  exact forall_step_exists_word t a b

instance instDecDistinct : Decidable (distinct t a b) := by
  apply decidable_of_iff (∃ w : word σs, ¬(δ_star' t a w ∈ t.fs ↔ δ_star' t b w ∈ t.fs))
  apply Iff.symm
  apply distinct_iff_ex_notaccepted

instance instDecNondistinct : Decidable (nondistinct t a b) := by
  simp only [nondistinct]
  infer_instance

-- Minimization of DFA using nondistinct states (table filling algorithm)

def min_q : Finset (Finset qs) := qs.attach.biUnion (fun q => {qs.attach.filter (fun q' => nondistinct t q' q)})

def min_init : { x // x ∈ min_q t } := by
  simp only [min_q]
  exact ⟨qs.attach.filter (fun q => nondistinct t q t.s), by rw [Finset.mem_biUnion]; exists t.s; rw [Finset.mem_singleton]; exact ⟨by simp, rfl⟩⟩

def min_fs : Finset { x // x ∈ min_q t } := (min_q t).attach.filter (fun f => ∃ q : qs, q ∈ f.1 ∧ q ∈ t.fs)

theorem min_δ_step_in (a : { x // x ∈ min_q t }) : a.1.biUnion (fun a => (qs.attach).filter (fun b => nondistinct t b (t.δ a e))) ∈ min_q t := by
  simp only [min_q]
  simp only [min_q] at a
  have := a.2
  rw [Finset.mem_biUnion] at this
  apply Exists.elim this
  intro q ex
  rw [Finset.mem_singleton] at ex
  rw [Finset.mem_biUnion]
  exists (t.δ q e)
  apply And.intro
  · simp
  · rw [Finset.mem_singleton]
    apply mem_iff_mem_eq
    intro el
    rw [ex.2]
    rw [Finset.mem_biUnion,Finset.mem_filter]
    apply Iff.intro
    · intro elin
      apply Exists.elim elin
      intro q₁ h
      rw [Finset.mem_filter,Finset.mem_filter] at h
      have : nondistinct t (t.δ q₁ e) (t.δ q e) := nondistinct_step t h.1.2
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


def min_δ : { x // x ∈ min_q t } → { x // x ∈ σs } → { x // x ∈ min_q t } := by
  intro a e
  let b := a.1.biUnion (fun a => (qs.attach).filter (fun b => nondistinct t b (t.δ a e)))
  exact ⟨b , min_δ_step_in t a⟩

def min_dfa : DFA σs (min_q t) := {s := min_init t, fs := min_fs t, δ := min_δ t}

def state_eq_class (a : qs) : { x // x ∈ (min_q t) } := ⟨qs.attach.filter (fun q => nondistinct t q a), by simp [min_dfa,min_q]; exists a; exists (by simp)⟩

lemma step_eq_class_eq : state_eq_class t (DFA.δ t a e) = DFA.δ (min_dfa t) (state_eq_class t a) e := by
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
    · exact ⟨by simp, nondistinct_self t⟩
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

theorem min_δ'_accepts_iff {w : word σs} : {a : qs} → (δ_star' t a w ∈ t.fs ↔ δ_star' (min_dfa t) (state_eq_class t a) w ∈ (min_dfa t).fs) := by
  induction w with
  | nil => intro a
           simp only [δ_star',state_eq_class,min_dfa,min_fs,min_q,Finset.mem_filter]
           simp [Finset.mem_filter]
           apply Iff.intro
           · intro ain
             apply And.intro
             · simp only [min_q]
               apply Finset.mem_attach
             · exists a
               apply Exists.intro
               · exact ⟨nondistinct_self t, ain⟩
               · simp
           · intro h
             apply Exists.elim h.2
             intro q h
             apply Exists.elim h
             intro qin h
             have := (nondistinct_iff_forall_accepted t).mp h.1 []
             apply this.mp
             exact h.2
  | cons e es s => intro a
                   simp only [δ_star']
                   have : (state_eq_class t (t.δ a e)) = (DFA.δ (min_dfa t) (state_eq_class t a) e) := step_eq_class_eq t
                   rw [←this]
                   apply s

theorem min_eq {w : word σs} : dfa_accepts t w ↔ dfa_accepts (min_dfa t) w := by
  simp only [dfa_accepts,δ_star]
  apply min_δ'_accepts_iff

theorem min_reachable_min_eq {w : word σs} : dfa_accepts (minimization_reachable t) w ↔ dfa_accepts (min_dfa (minimization_reachable t)) w := by
  apply min_eq

theorem min_min_eq {w : word σs} : dfa_accepts t w ↔ dfa_accepts (min_dfa (minimization_reachable t)) w := by
  apply Iff.intro
  · intro d
    apply (min_reachable_min_eq t).mp
    apply (minimization_reachable_eq t).mp
    exact d
  · intro d
    apply (minimization_reachable_eq t).mpr
    apply (min_reachable_min_eq t).mpr
    exact d

theorem ex_unreachable_iff_notminimal : (∃ q : qs, ¬(reachable t t.s q)) ↔ (minimization_reachable_q t).card < qs.card := by
  apply Iff.intro
  · intro ex
    apply Exists.elim ex
    intro a h
    simp only [minimization_reachable,minimization_reachable_q]
    have : card (qs.attach) = card qs := by apply Finset.card_attach
    rw [←this]
    apply Finset.card_lt_card
    apply Finset.filter_ssubset.mpr
    exists a
    apply And.intro
    · simp
    · exact h
  · intro lt
    simp only [minimization_reachable] at lt
    have : card (qs.attach) = card qs := by apply Finset.card_attach
    rw [←this] at lt
    have h : minimization_reachable_q t ≠ qs.attach := by intro eq
                                                          rw [←eq] at lt
                                                          apply Nat.lt_irrefl
                                                          exact lt
    have : minimization_reachable_q t ⊆ qs.attach := by simp [minimization_reachable_q]
    have : minimization_reachable_q t ⊂ qs.attach := by apply Finset.ssubset_iff_subset_ne.mpr
                                                        exact ⟨this,h⟩
    have := Finset.ssubset_iff_exists_cons_subset.mp this
    apply Exists.elim this
    intro a ex
    apply Exists.elim ex
    intro nin _
    simp only [minimization_reachable_q,Finset.mem_filter,not_and] at nin
    exists a
    apply nin
    apply Finset.mem_attach

theorem all_rechable_or : (∀ q : qs, reachable t t.s q) → ∀ q : qs, q = t.s ∨ ∃ q₂ : qs, ∃ s : σs, t.δ q₂ s = q := by
  intro fa
  intro q
  have := fa q
  cases this with
  | base => apply Or.inl
            rfl
  | step a r e => apply Or.inr
                  exists a
                  exists e

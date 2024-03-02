import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.FinEnum

namespace Finset

variable {α β : Type _} [DecidableEq α]

theorem nonempty_inter_singleton_imp_in (e : α) (es : Finset α) :
  Finset.Nonempty ({e} ∩ es) → e ∈ es := by
    intro ne
    have h₁ : e ∉ es → {e} ∩ es = ∅ := Finset.singleton_inter_of_not_mem
    have h₂ := Not.imp_symm h₁
    apply h₂
    apply (Iff.mp Finset.nonempty_iff_ne_empty)
    exact ne

theorem in_nonempty_inter_singleton (e : α) (es : Finset α) : e ∈ es → Finset.Nonempty ({e} ∩ es) := by
  intro ein
  rw [Finset.inter_comm,Finset.inter_singleton_of_mem ein]
  exact Finset.singleton_nonempty e

theorem subtype_of_finset_to_finset {fα : Finset α} : Finset {a  // a ∈ fα} → Finset α := fun f => f.map ⟨ fun a => a.1 , by simp [Function.Injective]⟩

def fin_of_subtype_to_subtype_of_subfin {qs : Finset α} (s : Finset { x // x ∈ qs }) : { x // x ⊆ Finset.attach qs } := by
  exact ⟨s , fun x => by simp⟩

def subtype_of_subfin_to_fin_of_subtype {qs : Finset α}  (s : { x // x ⊆ Finset.attach qs }) : (Finset { x // x ∈ qs }) := by
  exact s.1

def subtype_of_sset_subtype {α : Type _} {s ss : Finset α} (e : { x // x ∈ ss}) : ss ⊆ s → { x // x ∈ s} := by
  intro iss
  exact ⟨e.1 , by simp; apply Finset.mem_of_subset iss; exact e.2⟩

theorem filter_eq_filter {α : Type _} [DecidableEq α] (f : Finset α) (P A : α → Prop) [DecidablePred P] [DecidablePred A] (h : ∀ a : α, P a ↔ A a) : f.filter P = f.filter A := by
  induction f using Finset.induction_on with
  | empty => trivial
  | insert _ eq => rw [Finset.insert_eq,Finset.filter_union,Finset.filter_union,eq]
                   have : (a : α) → Finset.filter P {a} = Finset.filter A {a} := by intro a
                                                                                    rw [Finset.filter_singleton,Finset.filter_singleton]
                                                                                    split_ifs
                                                                                    · rfl
                                                                                    · have : A a := by apply (h a).mp
                                                                                                       assumption
                                                                                      contradiction
                                                                                    · have : P a := by apply (h a).mpr
                                                                                                       assumption
                                                                                      contradiction
                                                                                    · rfl
                   rw [this]

theorem mem_iff_insert_mem_iff_sdiff {α : Type _} [DecidableEq α] {a : α} {fa fb : Finset α} (h₁ : a ∉ fa) (h₂ : ∀ e, e ∈ insert a fa ↔ e ∈ fb) : (∀ e , e ∈ fa ↔ e ∈ (fb \ {a})) := by
  intro e
  apply Iff.intro
  · intro ein
    apply Finset.mem_sdiff.mpr
    apply And.intro
    · apply (h₂ e).mp
      apply Finset.mem_insert.mpr
      apply Or.inr
      exact ein
    have : e ≠ a := by intro eq
                       rw [eq] at ein
                       contradiction
    rw [Finset.mem_singleton]
    exact this
  · intro ein
    rw [Finset.mem_sdiff] at ein
    have := (h₂ e).mpr ein.1
    rw [Finset.mem_insert] at this
    apply Or.elim this
    · intro eq
      have : e ≠ a := by apply Finset.not_mem_singleton.mp
                         exact ein.2
      contradiction
    · intro h
      exact h

lemma mem_iff_mem_eq_lemma {α : Type _} [DecidableEq α] {b : α} {f : Finset α} : (∀ (a : α), a ∈ (∅ : Finset α) ↔ a ∈ insert b f) → False := by
  intro fa
  have : b ∈ ∅ := by apply (fa b).mpr
                     apply Finset.mem_insert_self
  contradiction

theorem mem_iff_mem_eq : {fa fb : Finset α} → (h : ∀ a : α, a ∈ fa ↔ a ∈ fb) → fa = fb := by
  intro fa
  induction fa using Finset.induction_on with
  | empty => intro fb h
             induction fb using Finset.induction_on with
             | empty => rfl
             | insert _ eq => rw [eq]
                              exfalso
                              exact mem_iff_mem_eq_lemma h
                              intro a
                              apply Iff.intro
                              · intro einf
                                contradiction
                              · intro ain
                                apply (h a).mpr
                                apply Finset.mem_insert.mpr
                                apply Or.inr
                                exact ain
  | insert _ eq =>  intro fb h
                    rw [Finset.insert_eq]
                    have := (mem_iff_insert_mem_iff_sdiff (by assumption) h)
                    have := eq this
                    rw [this]
                    rw [Finset.union_comm,Finset.sdiff_union_self_eq_union]
                    apply Finset.union_eq_left_iff_subset.mpr
                    apply Finset.singleton_subset_set_iff.mpr
                    apply (h _).mp
                    apply Finset.mem_insert_self

theorem eq_mem_iff_mem  : {fa fb : Finset α} → fa = fb → ∀ a : α, a ∈ fa ↔ a ∈ fb := by
  intro fa fb eq
  rw [eq]
  simp

theorem eq_iff_fa_mem {fa fb : Finset α} : fa = fb ↔ ∀ a : α, a ∈ fa ↔ a ∈ fb := by
  apply Iff.intro
  · apply eq_mem_iff_mem
  · apply mem_iff_mem_eq


theorem biUnion_union [DecidableEq β] (a b : Finset α) (f : α → Finset β) : Finset.biUnion (a ∪ b) f = (Finset.biUnion a f) ∪ (Finset.biUnion b f) := by
  apply eq_iff_fa_mem.mpr
  intro e
  rw [Finset.mem_union,Finset.mem_biUnion,Finset.mem_biUnion,Finset.mem_biUnion]
  apply Iff.intro
  · intro ein
    apply Exists.elim ein
    intro q qin
    rw [Finset.mem_union] at qin
    apply Or.elim qin.1
    · intro qina
      apply Or.inl
      exists q
      use qina
      exact qin.2
    · intro qinb
      apply Or.inr
      exists q
      use qinb
      exact qin.2
  · intro h
    apply Or.elim h
    · intro ex
      apply Exists.elim ex
      intro e ein
      exists e
      exact ⟨mem_union_left _ ein.1,ein.2⟩
    · intro ex
      apply Exists.elim ex
      intro e ein
      exists e
      exact ⟨mem_union_right _ ein.1,ein.2⟩


theorem nonempty_inter_subset {a b c : Finset α} (h : a ⊆ c) : Finset.Nonempty (a ∩ b) → Finset.Nonempty (c ∩ b) := by
  intro ne
  rw [Finset.Nonempty]
  rw [Finset.Nonempty] at ne
  apply Exists.elim ne
  intro x xin
  exists x
  apply Finset.mem_inter.mpr
  rw [Finset.mem_inter] at xin
  apply And.intro
  · apply Finset.mem_of_subset
    · exact h
    · exact xin.1
  · exact xin.2

end Finset

import Mathlib.Data.Finset.Sum
import Mathlib.Logic.Embedding.Basic
import Automaton.NFA.Basic

open NFA

namespace Append

variable {σ : Type _} {q₁ q₂ : Type _} {σs : Finset σ}  [DecidableEq q₁] [DecidableEq q₂] (t : NFA σs) (s : NFA σs) [DecidableEq σ] (xs : Finset {x // x ∈ σs}) (w : word σs)

def append_qs : Finset ({ x // x ∈ t.qs } ⊕ { x // x ∈ s.qs }) := Finset.disjSum t.qs.attach s.qs.attach

def all_in_qs  (q :  { x // x ∈ t.qs } ⊕ { x // x ∈ s.qs }) : q ∈ append_qs t s := by
  simp only [append_qs]
  cases q with
  | inl h => apply Finset.inl_mem_disjSum.mpr
             simp
  | inr h => apply Finset.inr_mem_disjSum.mpr
             simp

def lift_inl (f : Finset {x // x ∈ t.qs}) : Finset {x // x ∈ append_qs t s} := by
  exact f.map ⟨fun q => ⟨Sum.inl q,all_in_qs _ _ _⟩, by simp [Function.Injective]⟩

def lift_inr (f : Finset {x // x ∈ s.qs}) : Finset {x // x ∈ append_qs t s} := by
  exact f.map ⟨fun q => ⟨Sum.inr q,all_in_qs _ _ _⟩, by simp [Function.Injective]⟩

def append_q₀ : Finset { x // x ∈ append_qs t s } :=
  if nfa_accepts t [] then lift_inl t s t.q₀ ∪ lift_inr t s s.q₀
  else lift_inl t s t.q₀

def append_fs : Finset { x // x ∈ append_qs t s } := lift_inr t s s.fs

def append_δ : { x // x ∈ append_qs t s } → { x // x ∈ σs } → Finset { x // x ∈ append_qs t s } := by
  intro q e
  cases q.1 with
  | inl h => if (t.δ h e ∩ t.fs).Nonempty then exact lift_inl t s (t.δ h e) ∪ lift_inr t s s.q₀ else exact lift_inl t s (t.δ h e)
  | inr h => exact lift_inr t s (s.δ h e)


def append_nfa : NFA σs  := {qs := append_qs t s, q₀ := append_q₀ t s, fs:= append_fs t s, δ := append_δ t s}

lemma fs_eq : append_fs t s = lift_inr t s s.fs := by simp [append_fs]

lemma append_nfa_fs_eq : (append_nfa t s).fs = lift_inr t s s.fs := by simp [append_nfa,append_fs]

lemma append_nfa_q₀_eq ( h : nfa_accepts t []) : (append_nfa t s).q₀ = lift_inl t s t.q₀ ∪ lift_inr t s s.q₀ := by
  simp only [append_nfa,append_q₀]
  split
  · simp [lift_inl,lift_inr,Finset.disjSum]
  · simp [lift_inl,lift_inr,Finset.disjSum]


theorem inl_mem_iff : (a : t.qs) → a ∈ δ_star' t t.q₀ w ↔ ⟨Sum.inl a, all_in_qs _ _ _⟩ ∈ δ_star' (append_nfa t s) (append_q₀ t s) w := by
  induction w using List.reverseRecOn with
  | H0  => intro a
           apply Iff.intro
           · intro h
             simp only [append_q₀,δ_star']
             simp only [append_q₀,δ_star'] at h
             split
             · simp only [Finset.mem_union]
               apply Or.inl
               simp [lift_inl]
               exact h
             · simp [lift_inl]
               exact h
           · intro ein
             simp only [δ_star',append_q₀] at ein
             simp only [δ_star']
             split at ein
             · simp at ein
               apply Or.elim ein
               · intro h
                 simp [lift_inl] at h
                 exact h
               · intro h
                 simp [lift_inr] at h
             · simp [lift_inl] at ein
               exact ein
  | H1 es e s => intro q
                 simp only [δ_star',δ_step,←δ_star'_append_eq,Finset.mem_biUnion]
                 apply Iff.intro
                 · intro h
                   apply Exists.elim h
                   intro a ain
                   exists ⟨Sum.inl a, all_in_qs _ _ _⟩
                   apply And.intro
                   · exact (s a).mp ain.1
                   · simp only [append_nfa,append_δ]
                     split
                     · apply Finset.mem_union_left
                       simp [lift_inl]
                       exact ain.2
                     · simp [lift_inl]
                       exact ain.2
                 · intro h
                   apply Exists.elim h
                   intro a ain
                   simp only [append_nfa,append_qs] at a
                   have := a.2
                   rw [Finset.mem_disjSum] at this
                   cases this with
                   | inl h => apply Exists.elim h
                              intro b bin
                              have aeq : ⟨Sum.inl b, by simp⟩ = a := by rw [Subtype.mk_eq_mk]; exact bin.2
                              rw [←aeq] at ain
                              have := (s _).mpr ain.1
                              exists b
                              simp [append_nfa,append_δ] at ain
                              split at ain
                              · rw [Finset.mem_union] at ain
                                apply Or.elim ain.2
                                · intro ain
                                  simp [lift_inl] at ain
                                  exact ⟨this,ain⟩
                                · intro ain
                                  simp [lift_inr] at ain
                              · simp [lift_inl] at ain
                                exact ⟨this,ain.2⟩
                   | inr h => apply Exists.elim h
                              intro b bin
                              have aeq : ⟨Sum.inr b, by simp⟩ = a := by rw [Subtype.mk_eq_mk]; exact bin.2
                              rw [←aeq] at ain
                              simp [append_nfa,append_δ,lift_inr] at ain



theorem s₀_subset : nfa_accepts t w → lift_inr t s s.q₀ ⊆ δ_star (append_nfa t s) w := by
  induction w using List.reverseRecOn with
  | H0  => simp only [nfa_accepts,append_nfa,lift_inr,append_q₀,δ_star,δ_star']
           intro ne
           split
           rw [Finset.subset_iff]
           intro x ex
           rw [Finset.mem_union]
           apply Or.inr
           · exact ex
           · contradiction
  | H1 es e _ =>  simp only [nfa_accepts,δ_star,←δ_star'_append_eq]
                  intro h
                  rw [Finset.subset_iff]
                  intro x ex
                  simp only [Finset.Nonempty] at h
                  apply Exists.elim h
                  intro a ain
                  simp only [δ_star',δ_step] at ain
                  rw [Finset.mem_inter,Finset.mem_biUnion] at ain
                  simp only [lift_inr,Finset.mem_map] at ex
                  apply Exists.elim ex
                  intro q' qin'
                  rw [←qin'.2]
                  simp only [Function.Embedding.coeFn_mk,δ_star',δ_step,append_nfa,Finset.mem_biUnion]
                  apply Exists.elim ain.1
                  intro b bin
                  exists ⟨Sum.inl b, all_in_qs _ _ _⟩
                  apply And.intro
                  · apply (inl_mem_iff t s _ _).mp
                    exact bin.1
                  · simp only [append_δ]
                    split
                    · simp [Finset.mem_union,lift_inr]
                      apply Or.inr
                      exact qin'.1
                    · exfalso
                      have : ¬ (t.δ b e ∩ t.fs).Nonempty := by assumption
                      apply this
                      rw [Finset.Nonempty]
                      exists a
                      rw [Finset.mem_inter]
                      exact ⟨bin.2,ain.2⟩


theorem ss_inr_δ_star (h : lift_inr t s s.q₀ ⊆ f) : lift_inr t s (δ_star s w) ⊆ δ_star' (append_nfa t s) f w := by
  induction w using List.reverseRecOn with
  | H0 => simp; exact h
  | H1 es e s => simp only [δ_star,←δ_star'_append_eq,δ_star',δ_step]
                 rw [Finset.subset_iff]
                 intro x xin
                 simp only [lift_inr,Finset.mem_map] at xin
                 apply Exists.elim xin
                 intro a ain
                 rw [←ain.2]
                 simp only [Function.Embedding.coeFn_mk,append_nfa,Finset.mem_biUnion]
                 simp only [lift_inr,Finset.mem_map,Finset.subset_iff] at s
                 rw [Finset.mem_biUnion] at ain
                 apply Exists.elim ain.1
                 intro a' ain'
                 have := @s ⟨Sum.inr a', all_in_qs _ _ _⟩ (by exists a'; simp only [δ_star]; exact ⟨ain'.1,rfl⟩)
                 exists ⟨Sum.inr a', all_in_qs _ _ _⟩
                 apply And.intro
                 · exact this
                 · simp [append_δ,lift_inr]
                   exact ain'.2


theorem accepts_if_s₀_ss (h : lift_inr t s s.q₀ ⊆ f) (nem : (δ_star s w ∩ s.fs).Nonempty) : (δ_star' (append_nfa t s) f w ∩ (append_nfa t s).fs).Nonempty := by
  have ne : (lift_inr t s (δ_star s w) ∩ lift_inr t s (s.fs)).Nonempty := by
    rw [Finset.Nonempty] at nem
    simp only [Finset.Nonempty,lift_inr]
    apply Exists.elim nem
    intro x xin
    exists ⟨Sum.inr x, all_in_qs _ _ _⟩
    rw [Finset.mem_inter,Finset.mem_map,Finset.mem_map]
    rw [Finset.mem_inter] at xin
    apply And.intro
    · exists x
      use xin.1
      simp
    · exists x
      use xin.2
      simp
  have ss₁ : lift_inr t s (δ_star s w) ⊆ δ_star' (append_nfa t s) f w := ss_inr_δ_star t s w h
  have ss₂ : lift_inr t s s.fs ⊆ (append_nfa t s).fs := by simp [lift_inr,append_nfa,append_fs]
  apply Finset.nonempty_inter_subset
  · exact ss₁
  · exact ss₂
  · exact ne


theorem ex_inr_fs' : ¬(∃ e, ⟨Sum.inr e,all_in_qs _ _ _⟩ ∈ δ_star (append_nfa t s) w ∧ ⟨Sum.inr e, all_in_qs _ _ _⟩ ∈ (append_nfa t s).fs) → ¬nfa_accepts (append_nfa t s) w := by
  intro nex
  rw [not_exists] at nex
  cases Decidable.em (nfa_accepts (append_nfa t s) w) with
  | inl h => simp only [nfa_accepts,Finset.Nonempty,append_nfa_fs_eq] at h
             exfalso
             apply Exists.elim h
             intro x xin
             simp only [Finset.mem_inter,lift_inr,Finset.mem_map] at xin
             apply Exists.elim xin.2
             intro a ain
             rw [←ain.2] at xin
             simp at xin
             simp only [δ_star]
             apply nex a
             apply And.intro
             · exact xin.1
             · simp [append_nfa_fs_eq,lift_inr]
               exact xin.2
  | inr h => exact h

theorem ex_inr_fs : nfa_accepts (append_nfa t s) w → (∃ e, ⟨Sum.inr e,all_in_qs _ _ _⟩ ∈ δ_star (append_nfa t s) w ∧ ⟨Sum.inr e, all_in_qs _ _ _⟩ ∈ (append_nfa t s).fs) := by
  rw [←Decidable.not_imp_not]
  apply ex_inr_fs'


theorem ex_split_start : (e : s.qs) → ⟨Sum.inr e,all_in_qs _ _ _⟩ ∈ δ_star (append_nfa t s) w → ∃ a b, nfa_accepts t a ∧ e ∈ δ_star s b ∧ a ++ b = w := by
  induction w using List.reverseRecOn with
  | H0  => intro e
           intro ex
           simp only [δ_star,δ_star',append_nfa,append_q₀] at ex
           split at ex
           · simp only [Finset.mem_union] at ex
             apply Or.elim ex
             · intro h
               simp [lift_inl] at h
             · intro h
               simp [lift_inr] at h
               exists []
               exists []
           · simp only [lift_inl,Finset.mem_map] at ex
             apply Exists.elim ex
             intro a ain
             simp at ain
  | H1 es e s => intro q qin
                 simp only [δ_star,←δ_star'_append_eq,δ_star',δ_step,Finset.mem_biUnion] at qin
                 apply Exists.elim qin
                 intro a ain
                 simp only [append_nfa,append_qs] at a
                 have := a.2
                 rw [Finset.mem_disjSum] at this
                 apply Or.elim this
                 · intro ex
                   apply Exists.elim ex
                   intro b bin
                   have aeq : ⟨Sum.inl b, by simp⟩ = a := by rw [Subtype.mk_eq_mk]; exact bin.2
                   rw [←aeq] at ain
                   have oain := ain
                   simp [append_nfa,append_δ] at ain
                   split at ain
                   · rw [Finset.mem_union] at ain
                     apply Or.elim ain.2
                     · intro xin
                       simp [lift_inl] at xin
                     · intro xin
                       exists es++[e]
                       exists []
                       simp only [nfa_accepts,δ_star,←δ_star'_append_eq,δ_star']
                       apply And.intro
                       · have bin := (inl_mem_iff _ _ _ _).mpr oain.1
                         simp [lift_inr] at xin
                         simp only [Finset.Nonempty,δ_step]
                         have : (t.δ b e ∩ t.fs).Nonempty := by assumption
                         rw [Finset.Nonempty] at this
                         apply Exists.elim this
                         intro c cin
                         exists c
                         rw [Finset.mem_inter]
                         rw [Finset.mem_inter] at cin
                         apply And.intro
                         · rw [Finset.mem_biUnion]
                           exists b
                           use bin
                           exact cin.1
                         · exact cin.2
                       · simp [lift_inr] at xin
                         use xin
                         simp
                   · simp [lift_inl] at ain
                 · intro ex
                   apply Exists.elim ex
                   intro b bin
                   have aeq : ⟨Sum.inr b, by simp⟩ = a := by rw [Subtype.mk_eq_mk]; exact bin.2
                   rw [←aeq] at ain
                   have := s _ ain.1
                   apply Exists.elim this
                   intro a ex
                   apply Exists.elim ex
                   intro b' h
                   exists a
                   exists b'++[e]
                   use h.1
                   rw [←List.append_assoc,h.2.2]
                   apply And.intro
                   · simp only [δ_star,←δ_star'_append_eq,δ_star',δ_step,Finset.mem_biUnion]
                     simp [append_nfa,append_δ,lift_inr] at ain
                     exists b
                     apply And.intro
                     · simp only [δ_star] at h
                       exact h.2.1
                     · exact ain.2
                   · rfl


theorem ex_split : nfa_accepts (append_nfa t s) w → ∃ a b, nfa_accepts t a ∧ nfa_accepts s b ∧ a ++ b = w := by
  intro acc
  have := ex_inr_fs t s _ acc
  apply Exists.elim this
  intro e ein
  have := ex_split_start t s _ _ ein.1
  apply Exists.elim this
  intro a ex
  apply Exists.elim ex
  intro b h
  exists a
  exists b
  use h.1
  apply And.intro
  · simp only [nfa_accepts,Finset.Nonempty]
    exists e
    rw [Finset.mem_inter]
    apply And.intro
    · exact h.2.1
    · simp [append_nfa_fs_eq,lift_inr] at ein
      exact ein.2
  · exact h.2.2


theorem accepts_if_split : nfa_accepts t a ∧ nfa_accepts s b → nfa_accepts (append_nfa t s) (a++b) := by
  simp only [nfa_accepts,δ_star,←δ_star'_append_eq]
  intro h'
  apply accepts_if_s₀_ss
  · apply s₀_subset
    simp only [nfa_accepts]
    exact h'.1
  · exact h'.2


theorem accepts_iff : nfa_accepts (append_nfa t s) w ↔ ∃ a b, nfa_accepts t a ∧ nfa_accepts s b ∧ a++b=w := by
  apply Iff.intro
  · apply ex_split
  · intro ex
    apply Exists.elim ex
    intro a ex
    apply Exists.elim ex
    intro b h
    rw [←h.2.2]
    apply accepts_if_split
    exact ⟨h.1,h.2.1⟩

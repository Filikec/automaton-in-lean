import Automaton.NFA.Basic
import Automaton.NFA.ToDFA
import Automaton.Regex.Basic
import Automaton.DFA.Basic
import Automaton.Language.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Logic.Embedding.Basic

open NFA

namespace Plus

variable {σ : Type _} {q₁ q₂ : Type _} {σs : Finset σ}  [DecidableEq q₁] [DecidableEq q₂] (t s : NFA σs) [DecidableEq σ] (xs : Finset {x // x ∈ σs})

def plus_qs : Finset ({ x // x ∈ t.qs } ⊕ { x // x ∈ s.qs }) := Finset.disjSum t.qs.attach s.qs.attach

def all_in_qs  (q :  { x // x ∈ t.qs } ⊕ { x // x ∈ s.qs }) : q ∈ plus_qs t s := by
  simp only [plus_qs]
  cases q with
  | inl h => apply Finset.inl_mem_disjSum.mpr
             simp
  | inr h => apply Finset.inr_mem_disjSum.mpr
             simp

def lift_inl (f : Finset {x // x ∈ t.qs}) : Finset {x // x ∈ plus_qs t s} := by
  exact f.map ⟨fun q => ⟨Sum.inl q,all_in_qs _ _ _⟩,by simp [Function.Injective]⟩

def lift_inr (f : Finset {x // x ∈ s.qs}) : Finset {x // x ∈ plus_qs t s} := by
  exact f.map ⟨fun q => ⟨Sum.inr q,all_in_qs _ _ _⟩,by simp [Function.Injective]⟩

def plus_q₀ : Finset { x // x ∈ plus_qs t s } := (Finset.disjSum t.q₀ s.q₀).map ⟨(fun q => ⟨q , all_in_qs _ _ _⟩), by simp [Function.Injective]⟩

def plus_fs : Finset { x // x ∈ plus_qs t s } := (Finset.disjSum t.fs s.fs).map ⟨(fun q => ⟨q , all_in_qs _ _ _⟩), by simp [Function.Injective]⟩

def plus_δ : { x // x ∈ plus_qs t s } → { x // x ∈ σs } → Finset { x // x ∈ plus_qs t s } := by
  intro q e
  cases q.1 with
  | inl h => exact lift_inl t s (t.δ h e)
  | inr h => exact lift_inr t s (s.δ h e)


def plus_nfa : NFA σs  := {qs := plus_qs t s, q₀ := plus_q₀ t s, fs:= plus_fs t s, δ := plus_δ t s}

theorem plus_eq : δ_star (plus_nfa t s) w = lift_inl t s (δ_star t w) ∪ lift_inr t s (δ_star s w) := by
  induction w using List.reverseRecOn with
  | H0 => apply Finset.ext_iff.mpr
          intro q
          simp only [δ_star,δ_star',plus_nfa,plus_q₀,lift_inl,lift_inr,Finset.mem_union]
          apply Iff.intro
          · intro h'
            rw [Finset.mem_map] at h'
            apply Exists.elim h'
            intro a ain
            rw [Finset.mem_disjSum] at ain
            apply Or.elim ain.1
            · intro ex
              apply Exists.elim ex
              intro b bin
              apply Or.inl
              apply Finset.mem_map.mpr
              exists b
              apply And.intro
              · exact bin.1
              · rw [←ain.2]
                simp
                exact bin.2
            · intro ex
              apply Exists.elim ex
              intro b bin
              apply Or.inr
              apply Finset.mem_map.mpr
              exists b
              apply And.intro
              · exact bin.1
              · rw [←ain.2]
                simp
                exact bin.2
          · intro qin
            rw [Finset.mem_map]
            apply Or.elim qin
            · intro h
              rw [Finset.mem_map] at h
              apply Exists.elim h
              intro a ain
              exists Sum.inl a
              apply And.intro
              · apply Finset.mem_disjSum.mpr
                apply Or.inl
                exists a
                exact ⟨ain.1,rfl⟩
              · exact ain.2
            · intro h
              rw [Finset.mem_map] at h
              apply Exists.elim h
              intro a ain
              exists Sum.inr a
              apply And.intro
              · apply Finset.mem_disjSum.mpr
                apply Or.inr
                exists a
                exact ⟨ain.1,rfl⟩
              · exact ain.2
  | H1 es e s'=> simp only [δ_star,←δ_star'_append_eq,δ_star']
                 simp only [δ_star] at s'
                 rw [s']
                 have : ∀ q e, δ_step (plus_nfa t s) q e = δ_star' (plus_nfa t s) q [e] := by simp [δ_star']
                 rw [this,δ_star'_union]
                 apply Finset.ext_iff.mpr
                 intro q
                 simp only [plus_nfa,plus_qs] at q
                 have qsum := q.2
                 rw [Finset.mem_disjSum] at qsum
                 apply Or.elim qsum
                 · intro ex'
                   apply Exists.elim ex'
                   intro q' qe'
                   have : ⟨Sum.inl q',Finset.inl_mem_disjSum.mpr qe'.1⟩ = q := by rw [Subtype.mk_eq_mk]; exact qe'.2
                   rw [←this]
                   apply Iff.intro
                   · intro h
                     rw [Finset.mem_union] at h
                     rw [Finset.mem_union]
                     apply Or.inl
                     simp only [lift_inl,Finset.mem_map]
                     apply Or.elim h
                     · intro h'
                       simp only [lift_inl,δ_star',δ_step,Finset.mem_biUnion] at h'
                       apply Exists.elim h'
                       intro a ain
                       rw [Finset.mem_map] at ain
                       exists q'
                       apply And.intro
                       · simp only [δ_step]
                         rw [Finset.mem_biUnion]
                         apply Exists.elim ain.1
                         intro a _
                         simp [plus_nfa] at ain
                         apply Exists.elim ain.1
                         intro a ex
                         apply Exists.elim ex
                         intro b bin
                         rw [←bin.2] at ain
                         simp [plus_δ,lift_inl] at ain
                         exists ⟨a,b⟩
                         exact ⟨bin.1,by apply ain.2⟩
                       · simp
                     · intro h'
                       simp only [lift_inr,δ_star',δ_step,Finset.mem_biUnion] at h'
                       apply Exists.elim h'
                       intro a ain
                       rw [Finset.mem_map] at ain
                       exists q'
                       apply And.intro
                       · simp only [δ_step]
                         rw [Finset.mem_biUnion]
                         apply Exists.elim ain.1
                         intro a _
                         simp [plus_nfa] at ain
                         apply Exists.elim ain.1
                         intro a ex
                         apply Exists.elim ex
                         intro b bin
                         rw [←bin.2] at ain
                         simp [plus_δ,lift_inr] at ain
                       · simp
                   · intro h
                     rw [Finset.mem_union] at h
                     rw [Finset.mem_union]
                     apply Or.elim h
                     · intro h'
                       apply Or.inl
                       simp only [δ_star',δ_step,Finset.mem_biUnion]
                       simp only [lift_inl,Finset.mem_map] at h'
                       apply Exists.elim h'
                       intro a ain
                       simp at ain
                       apply Exists.elim ain.1
                       intro a ex
                       apply Exists.elim ex
                       intro b bin
                       exists ⟨Sum.inl ⟨a,b⟩,all_in_qs _ _ _⟩
                       simp [lift_inl,plus_nfa,plus_δ]
                       rw [←ain.2]
                       exact bin
                     · intro h'
                       apply Or.inr
                       simp only [δ_star',δ_step,Finset.mem_biUnion]
                       simp only [lift_inr,Finset.mem_map] at h'
                       apply Exists.elim h'
                       intro a ain
                       simp at ain
                 · intro ex'
                   apply Exists.elim ex'
                   intro q' qe'
                   have : ⟨Sum.inr q',Finset.inr_mem_disjSum.mpr qe'.1⟩ = q := by rw [Subtype.mk_eq_mk]; exact qe'.2
                   rw [←this]
                   apply Iff.intro
                   · intro h
                     rw [Finset.mem_union] at h
                     rw [Finset.mem_union]
                     apply Or.inr
                     simp only [lift_inr,Finset.mem_map]
                     apply Or.elim h
                     · intro h'
                       simp only [lift_inl,δ_star',δ_step,Finset.mem_biUnion] at h'
                       apply Exists.elim h'
                       intro a ain
                       rw [Finset.mem_map] at ain
                       exists q'
                       apply And.intro
                       · simp only [δ_step]
                         rw [Finset.mem_biUnion]
                         apply Exists.elim ain.1
                         intro a _
                         simp [plus_nfa] at ain
                         apply Exists.elim ain.1
                         intro a ex
                         apply Exists.elim ex
                         intro b bin
                         rw [←bin.2] at ain
                         simp [plus_δ,lift_inl] at ain
                       · simp
                     · intro h'
                       simp only [lift_inr,δ_star',δ_step,Finset.mem_biUnion] at h'
                       apply Exists.elim h'
                       intro a ain
                       rw [Finset.mem_map] at ain
                       exists q'
                       apply And.intro
                       · simp only [δ_step]
                         rw [Finset.mem_biUnion]
                         apply Exists.elim ain.1
                         intro a _
                         simp [plus_nfa] at ain
                         apply Exists.elim ain.1
                         intro a ex
                         apply Exists.elim ex
                         intro b bin
                         rw [←bin.2] at ain
                         simp [plus_δ,lift_inr] at ain
                         exists ⟨a,b⟩
                         exact ⟨bin.1,ain.2⟩
                       · simp
                   · intro h
                     rw [Finset.mem_union] at h
                     rw [Finset.mem_union]
                     apply Or.elim h
                     · intro h'
                       apply Or.inl
                       simp only [δ_star',δ_step,Finset.mem_biUnion]
                       simp only [lift_inl,Finset.mem_map] at h'
                       apply Exists.elim h'
                       intro a ain
                       simp at ain
                     · intro h'
                       apply Or.inr
                       simp only [δ_star',δ_step,Finset.mem_biUnion]
                       simp only [lift_inr,Finset.mem_map] at h'
                       apply Exists.elim h'
                       intro a ain
                       simp at ain
                       apply Exists.elim ain.1
                       intro a ex
                       apply Exists.elim ex
                       intro b bin
                       exists ⟨Sum.inr ⟨a,b⟩,all_in_qs _ _ _⟩
                       simp [lift_inr,plus_nfa,plus_δ,Finset.mem_map]
                       rw [←ain.2]
                       exact bin


theorem accepts_iff : nfa_accepts (plus_nfa t s) w ↔ nfa_accepts t w ∨ nfa_accepts s w := by
  simp only [nfa_accepts]
  apply Iff.intro
  · intro h
    rw [plus_eq,Finset.Nonempty] at h
    rw [Finset.Nonempty]
    apply Exists.elim h
    intro x xin
    rw [Finset.mem_inter,Finset.mem_union] at xin
    apply Or.elim xin.1
    · intro xe
      apply Or.inl
      simp only [lift_inl,Finset.mem_map] at xe
      apply Exists.elim xe
      intro a h
      exists a
      rw [Finset.mem_inter]
      apply And.intro
      · exact h.1
      · rw [←h.2] at xin
        simp [plus_nfa,plus_fs] at xin
        apply xin.2
    · intro xe
      apply Or.inr
      simp only [lift_inr,Finset.mem_map] at xe
      apply Exists.elim xe
      intro a h
      exists a
      rw [Finset.mem_inter]
      apply And.intro
      · exact h.1
      · rw [←h.2] at xin
        simp [plus_nfa,plus_fs] at xin
        apply xin.2
  · intro h
    rw [plus_eq]
    rw [Finset.Nonempty]
    apply Or.elim h
    · intro h
      rw [Finset.Nonempty] at h
      apply Exists.elim h
      intro x xin
      rw [Finset.mem_inter] at xin
      exists ⟨Sum.inl x, all_in_qs _ _ _⟩
      rw [Finset.mem_inter,Finset.mem_union]
      apply And.intro
      · apply Or.inl
        simp [lift_inl]
        exact xin.1
      · simp [plus_nfa,plus_fs]
        exact xin.2
    · intro h
      rw [Finset.Nonempty] at h
      apply Exists.elim h
      intro x xin
      rw [Finset.mem_inter] at xin
      exists ⟨Sum.inr x, all_in_qs _ _ _⟩
      rw [Finset.mem_inter,Finset.mem_union]
      apply And.intro
      · apply Or.inr
        simp [lift_inr]
        exact xin.1
      · simp [plus_nfa,plus_fs]
        exact xin.2
end Plus

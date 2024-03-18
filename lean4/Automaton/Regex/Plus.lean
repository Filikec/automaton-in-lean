import Mathlib.Data.Finset.Sum
import Mathlib.Logic.Embedding.Basic
import Automaton.NFA.Basic

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
  exact f.map ⟨fun q => ⟨Sum.inl q,all_in_qs _ _ _⟩, by simp [Function.Injective]⟩

def lift_inr (f : Finset {x // x ∈ s.qs}) : Finset {x // x ∈ plus_qs t s} := by
  exact f.map ⟨fun q => ⟨Sum.inr q,all_in_qs _ _ _⟩, by simp [Function.Injective]⟩

def plus_q₀ : Finset { x // x ∈ plus_qs t s } := lift_inl t s t.q₀ ∪ lift_inr t s s.q₀

def plus_fs : Finset { x // x ∈ plus_qs t s } := lift_inl t s t.fs ∪ lift_inr t s s.fs

def plus_δ : { x // x ∈ plus_qs t s } → { x // x ∈ σs } → Finset { x // x ∈ plus_qs t s } := by
  intro q e
  cases q.1 with
  | inl h => exact lift_inl t s (t.δ h e)
  | inr h => exact lift_inr t s (s.δ h e)


def plus_nfa : NFA σs  := {qs := plus_qs t s, q₀ := plus_q₀ t s, fs:= plus_fs t s, δ := plus_δ t s}

theorem liftl_δ_step : lift_inl t s (δ_step t q e) = δ_step (plus_nfa t s) (lift_inl t s q) e:= by
  simp only [lift_inl,δ_step,plus_nfa]
  apply Finset.ext_iff.mpr
  intro a
  apply Iff.intro
  · intro h
    rw [Finset.mem_map] at h
    apply Exists.elim h
    intro a ain
    rw [Finset.mem_biUnion]
    rw [Finset.mem_biUnion] at ain
    apply Exists.elim ain.1
    intro b bin
    exists ⟨Sum.inl b, all_in_qs _ _ _⟩
    simp [plus_δ,lift_inl]
    use bin.1
    exists a
    exists (a.2)
    use bin.2
    exact ain.2
  · intro h
    simp [Finset.mem_biUnion,plus_qs,plus_δ] at h
    apply Exists.elim h
    intro b bin
    rw [Finset.mem_map]
    simp only [plus_qs] at a
    have := a.2
    simp only [Finset.mem_disjSum] at this
    apply Or.elim this
    · intro ex
      apply Exists.elim ex
      intro c cin
      exists c
      apply And.intro
      · rw [Finset.mem_biUnion]
        apply Exists.elim bin.2
        intro x xin
        simp [lift_inl] at xin
        apply Exists.elim xin
        intro d ex
        apply Exists.elim ex
        intro b' bh'
        exists ⟨b, x⟩
        apply Exists.elim bin.1
        intro x xh
        use xh
        have : ⟨Sum.inl c, all_in_qs _ _ _⟩  = a := by apply Subtype.eq; simp; apply cin.2
        rw [←bh'.2] at this
        simp at this
        rw [this]
        exact bh'.1
      · simp
        apply Subtype.eq
        simp
        apply cin.2
    · intro ex
      apply Exists.elim ex
      intro c cin
      apply Exists.elim bin.2
      intro x xh
      have : ⟨Sum.inr c, all_in_qs _ _ _⟩ = a := by apply Subtype.eq; simp; apply cin.2
      rw [←this] at xh
      simp [lift_inl] at xh


theorem liftr_δ_step : lift_inr t s (δ_step s q e) = δ_step (plus_nfa t s) (lift_inr t s q) e:= by
  simp only [lift_inr,δ_step,plus_nfa]
  apply Finset.ext_iff.mpr
  intro a
  apply Iff.intro
  · intro h
    rw [Finset.mem_map] at h
    apply Exists.elim h
    intro a ain
    rw [Finset.mem_biUnion]
    rw [Finset.mem_biUnion] at ain
    apply Exists.elim ain.1
    intro b bin
    exists ⟨Sum.inr b, all_in_qs _ _ _⟩
    simp [plus_δ,lift_inr]
    use bin.1
    exists a
    exists (a.2)
    use bin.2
    exact ain.2
  · intro h
    simp [Finset.mem_biUnion,plus_qs,plus_δ] at h
    apply Exists.elim h
    intro b bin
    rw [Finset.mem_map]
    simp only [plus_qs] at a
    have := a.2
    simp only [Finset.mem_disjSum] at this
    apply Or.elim this
    · intro ex
      apply Exists.elim ex
      intro c cin
      apply Exists.elim bin.2
      intro x xh
      have : ⟨Sum.inl c, all_in_qs _ _ _⟩ = a := by apply Subtype.eq; simp; apply cin.2
      rw [←this] at xh
      simp [lift_inr] at xh
    · intro ex
      apply Exists.elim ex
      intro c cin
      exists c
      apply And.intro
      · rw [Finset.mem_biUnion]
        apply Exists.elim bin.2
        intro x xin
        simp [lift_inr] at xin
        apply Exists.elim xin
        intro d ex
        apply Exists.elim ex
        intro b' bh'
        exists ⟨b, x⟩
        apply Exists.elim bin.1
        intro x xh
        use xh
        have : ⟨Sum.inr c, all_in_qs _ _ _⟩  = a := by apply Subtype.eq; simp; apply cin.2
        rw [←bh'.2] at this
        simp at this
        rw [this]
        exact bh'.1
      · simp
        apply Subtype.eq
        simp
        apply cin.2



theorem liftl_δ_star' : (q : Finset t.qs) → lift_inl t s (δ_star' t q w) = δ_star' (plus_nfa t s) (lift_inl t s q) w := by
  induction w with
  | nil => simp
  | cons e es s => simp only [δ_star']
                   intro q
                   rw [←liftl_δ_step]
                   apply s


theorem liftr_δ_star' : (q : Finset s.qs) → lift_inr t s (δ_star' s q w) = δ_star' (plus_nfa t s) (lift_inr t s q) w := by
  induction w with
  | nil => simp
  | cons e es s => simp only [δ_star']
                   intro q
                   rw [←liftr_δ_step]
                   apply s

theorem plus_eq : δ_star (plus_nfa t s) w = lift_inl t s (δ_star t w) ∪ lift_inr t s (δ_star s w) := by
  induction w using List.reverseRecOn with
  | H0 => apply Finset.ext_iff.mpr
          intro q
          simp only [δ_star,δ_star',plus_nfa,plus_q₀,lift_inl,lift_inr,Finset.mem_union]
  | H1 es e s'=> simp only [δ_star,←δ_star'_append_eq,δ_star']
                 simp only [δ_star] at s'
                 rw [s']
                 have : ∀ q e, δ_step (plus_nfa t s) q e = δ_star' (plus_nfa t s) q [e] := by simp [δ_star']
                 rw [this,δ_star'_union]
                 simp only [δ_star']
                 rw [liftr_δ_step,liftl_δ_step]


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
        simp [plus_nfa,plus_fs,lift_inl,lift_inr] at xin
        simp [lift_inl,lift_inr]
        exact xin.2
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
        simp [plus_nfa,plus_fs,lift_inl,lift_inr] at xin
        simp [lift_inl,lift_inr]
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
      · simp [plus_nfa,plus_fs,lift_inr,lift_inl]
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
      · simp [plus_nfa,plus_fs,lift_inr,lift_inl]
        exact xin.2
end Plus

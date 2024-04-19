import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Automaton.Regex.Basic
import Automaton.NFA.Basic
import Automaton.NFA.ToDFA

open NFA ToDFA

namespace Star

variable {σ : Type _} {q : Type _} {σs : Finset σ} (t : NFA σs) [DecidableEq σ] [DecidableEq q]


def star_nfa_δ : t.qs → σs → Finset t.qs := fun q σ => if Finset.Nonempty (t.δ q σ ∩ t.fs) then t.δ q σ ∪ t.q₀ else t.δ q σ

def star_nfa : NFA σs := {q₀ := t.q₀, fs := t.fs, δ := star_nfa_δ t}

lemma fs_eq : t.fs = (star_nfa t).fs := by simp [star_nfa]

lemma q₀_eq : t.q₀ = (star_nfa t).q₀ := by simp [star_nfa]

lemma δ_subset : t.δ s e ⊆ (star_nfa t).δ s e := by
  simp only [star_nfa,star_nfa_δ]
  split
  · apply Finset.subset_union_left
  · rfl

theorem subset_δ_star'_subset : (s₁ s₂ : Finset t.qs) → s₁ ⊆ s₂ → δ_star' t s₁ w ⊆ δ_star' t s₂ w := by
  induction w using List.reverseRecOn with
  | H0 => simp [δ_star']
  | H1 w e s => intro s₁ s₂ ss
                rw [←δ_star'_append_eq,←δ_star'_append_eq]
                have : δ_star' t s₁ w ⊆ δ_star' t s₂ w := by apply s; exact ss
                simp only [δ_star',δ_step,Finset.biUnion_subset]
                intro x xin
                apply Finset.subset_biUnion_of_mem (fun n => NFA.δ t n e)
                apply Finset.mem_of_subset
                apply this
                exact xin

theorem δ_step_subset (h : s₁ ⊆ s₂) : δ_step t s₁ e ⊆ δ_step (star_nfa t) s₂ e := by
  simp only [δ_step,Finset.biUnion_subset,star_nfa,star_nfa_δ,Finset.subset_iff]
  intro x xin
  rw [Finset.mem_biUnion]
  rw [Finset.mem_biUnion] at xin
  apply Exists.elim xin
  intro a ain
  exists a
  split
  · exact ⟨Finset.mem_of_subset h ain.1,Finset.mem_union_left _ ain.2⟩
  · exact ⟨Finset.mem_of_subset h ain.1,ain.2⟩


theorem δ_star'_subset : δ_star' t s w ⊆ δ_star' (star_nfa t) s w  := by
  induction w using List.reverseRecOn with
  | H0 => simp
  | H1 w e ss => rw [←δ_star'_append_eq,←δ_star'_append_eq]
                 simp only [δ_star',δ_star']
                 exact δ_step_subset t ss


theorem δ_step_inter_nonempty (q : Finset t.qs) : Finset.Nonempty (δ_step (star_nfa t) q e ∩ (star_nfa t).fs) ↔ Finset.Nonempty (δ_step t q e ∩ t.fs) := by
  apply Iff.intro
  · intro h
    rw [Finset.Nonempty] at h
    rw [Finset.Nonempty]
    apply Exists.elim h
    intro x xin
    rw [←fs_eq] at xin
    simp only [δ_step,Finset.mem_inter,Finset.mem_biUnion] at xin
    apply Exists.elim xin.1
    intro a ain
    simp only [star_nfa,star_nfa_δ] at ain
    split at ain
    · have : Finset.Nonempty (NFA.δ t a e ∩ t.fs) := by assumption
      rw [Finset.Nonempty] at this
      apply Exists.elim this
      intro b bin
      exists b
      simp only [δ_step,Finset.mem_inter,Finset.mem_biUnion]
      rw [Finset.mem_inter] at bin
      apply And.intro
      · exists a
        exact ⟨ain.1,bin.1⟩
      · exact bin.2
    · exists x
      simp only [δ_step,Finset.mem_inter,Finset.mem_biUnion]
      apply And.intro
      · exists a
      · exact xin.2
  · intro h
    apply Finset.nonempty_inter_subset
    · apply δ_step_subset _ (Finset.subset_of_eq (Eq.refl q))
    · simp only [star_nfa]; apply Finset.subset_of_eq (Eq.refl t.fs)
    · exact h


theorem δ_star'_eq_union (q : Finset t.qs) : Finset.Nonempty (δ_step t q e ∩ t.fs) → δ_star' (star_nfa t) q [e] = δ_star' t q [e] ∪ t.q₀ := by
  intro h
  simp only [δ_star,δ_star',δ_step]
  simp only [δ_step] at h
  simp only [star_nfa,star_nfa_δ]
  apply Finset.ext_iff.mpr
  intro q
  apply Iff.intro
  · intro h'
    rw [Finset.mem_biUnion] at h'
    rw [Finset.mem_union,Finset.mem_biUnion]
    apply Exists.elim h'
    intro x xin
    split at xin
    · rw [Finset.mem_union] at xin
      apply Or.elim xin.2
      · intro qin
        apply Or.inl
        exists x
        exact ⟨xin.1,qin⟩
      · intro qin
        apply Or.inr
        exact qin
    · apply Or.inl
      exists x
  · intro h'
    rw [Finset.mem_union,Finset.mem_biUnion] at h'
    rw [Finset.mem_biUnion]
    apply Or.elim h'
    · intro ex
      apply Exists.elim ex
      intro x xin
      exists x
      split
      · exact ⟨xin.1, Finset.mem_union_left _ xin.2⟩
      · exact xin
    · intro qin
      simp only [Finset.Nonempty] at h
      apply Exists.elim h
      intro a ain
      rw [Finset.mem_inter,Finset.mem_biUnion] at ain
      apply Exists.elim ain.1
      intro b bin
      exists b
      split
      · exact ⟨bin.1, Finset.mem_union_right _ qin⟩
      · exfalso
        have : ¬Finset.Nonempty (NFA.δ t b e ∩ t.fs) := by assumption
        apply this
        rw [Finset.Nonempty]
        exists a
        apply Finset.mem_inter.mpr
        exact ⟨bin.2, ain.2⟩

lemma δ_step_star_eq (q : Finset t.qs): ¬Finset.Nonempty (δ_step t q e ∩ t.fs) → δ_step (star_nfa t) q e = δ_step t q e := by
  intro ne
  simp only [star_nfa,star_nfa_δ,δ_step]
  rw [Finset.ext_iff]
  intro e'
  apply Iff.intro
  · intro ein
    rw [Finset.mem_biUnion] at ein
    rw [Finset.mem_biUnion]
    apply Exists.elim ein
    intro a ain
    split at ain
    · exfalso
      apply ne
      apply Finset.nonempty_inter_subset
      · exact δ_subset_δ_step t ain.1
      · apply Finset.subset_of_eq (Eq.refl _)
      · assumption
    · exists a
  · intro ein
    rw [Finset.mem_biUnion]
    rw [Finset.mem_biUnion] at ein
    apply Exists.elim ein
    intro a ain
    exists a
    apply And.intro
    · exact ain.1
    · split
      · exact Finset.mem_union_left _ ain.2
      · exact ain.2


theorem nfa_accepts_star_nfa : nfa_accepts t w → nfa_accepts (star_nfa t) w := by
  intro h
  simp only [nfa_accepts] at h
  simp only [nfa_accepts]
  apply Finset.nonempty_inter_subset
  · apply δ_star'_subset t
  · simp only [star_nfa]
    exact Finset.subset_of_eq (Eq.refl _)
  · exact h

theorem star_nfa_accepts_start_subset : nfa_accepts (star_nfa t) w → (star_nfa t).q₀ ⊆ δ_star (star_nfa t) w := by
  intro h
  cases List.eq_nil_or_concat w with
  | inl g => rw [g]
             simp [star_nfa]
  | inr g => apply Exists.elim g
             intro l ex
             apply Exists.elim ex
             intro a eq
             rw [eq] at h
             rw [eq,δ_star,←δ_star'_append_eq]
             simp only [nfa_accepts,δ_star,←δ_star'_append_eq,δ_star',←q₀_eq,δ_step_inter_nonempty] at h
             rw [←q₀_eq,δ_star'_eq_union]
             apply Finset.subset_union_right
             exact h

theorem star_nfa_accepts_append (a₁ : nfa_accepts (star_nfa t) w₁) (a₂ : nfa_accepts (star_nfa t) w₂) : nfa_accepts (star_nfa t) (w₁++w₂) := by
  simp only [nfa_accepts,δ_star]
  rw [←δ_star'_append_eq]
  simp only [nfa_accepts,δ_star,Finset.Nonempty] at a₂
  apply Exists.elim a₂
  intro q qin
  simp only [Finset.Nonempty]
  exists q
  rw [Finset.mem_inter] at qin
  apply Finset.mem_inter.mpr
  apply And.intro
  rw [←q₀_eq]
  · apply Finset.mem_of_subset
    · apply subset_δ_star'_subset _ _ _ (star_nfa_accepts_start_subset t a₁)
    · exact qin.1
  · exact qin.2


theorem accepts_or_ex_prefix_state : (q : Finset t.qs) → Finset.Nonempty (δ_star' (star_nfa t) q w ∩ (star_nfa t).fs) →
  (Finset.Nonempty (δ_star' t q w ∩ t.fs) ∨ ∃ a b, a ≠ [] ∧ a++b=w ∧ Finset.Nonempty (δ_star' t q a ∩ t.fs) ∧ b ∈ nfaLang (star_nfa t)) := by
  induction w with
  | nil=> simp only [nfaLang,nfa_accepts,δ_star,δ_star',δ_step]
          intro q
          apply Or.inl
  | cons e es s => intro q acc
                   simp only [nfaLang,Set.mem_def,nfa_accepts,δ_star] at acc
                   simp only [nfaLang,Set.mem_def,nfa_accepts,δ_star]
                   cases Decidable.em (Finset.Nonempty (δ_step t q e ∩ t.fs)) with
                   | inl h => have eq : δ_star' (star_nfa t) q [e] = δ_star' (star_nfa t) (δ_star' t q [e] ∪ t.q₀) [] := δ_star'_eq_union t q h
                              simp only [δ_star'] at eq
                              simp only [δ_star']
                              simp only [δ_star'] at acc
                              rw [eq,δ_star'_union] at acc
                              simp only [Finset.Nonempty] at acc
                              apply Exists.elim acc
                              intro x xin
                              rw [Finset.mem_inter,Finset.mem_union] at xin
                              apply Or.elim xin.1
                              · intro xins
                                have s' := s (δ_step t q e)
                                have : Finset.Nonempty (δ_star' (star_nfa t) (δ_step t q e) es ∩ (star_nfa t).fs) := by
                                  rw [Finset.Nonempty]
                                  exists x
                                  rw [Finset.mem_inter]
                                  exact ⟨xins,xin.2⟩
                                have := s' this
                                apply Or.elim this
                                · intro ne
                                  apply Or.inl
                                  exact ne
                                · intro ex
                                  apply Exists.elim ex
                                  intro a ex
                                  apply Exists.elim ex
                                  intro b bin
                                  apply Or.inr
                                  exists e::a
                                  exists b
                                  have : e :: a ≠ [] := by simp
                                  use this
                                  apply And.intro
                                  · rw [←bin.2.1]; simp
                                  · apply And.intro
                                    · exact bin.2.2.1
                                    · apply bin.2.2.2
                              · intro xins
                                apply Or.inr
                                exists [e]
                                exists es
                                have : [e] ≠ [] := by simp
                                use this
                                apply And.intro
                                · simp
                                · apply And.intro
                                  · apply h
                                  · simp only [Finset.Nonempty]
                                    exists x
                                    rw [Finset.mem_inter]
                                    exact ⟨xins,xin.2⟩
                   | inr h => simp only [δ_star'] at acc
                              simp only [δ_star']
                              have := s (δ_step (star_nfa t) q e) acc
                              rw [δ_step_star_eq] at this
                              apply Or.elim this
                              · intro e'
                                apply Or.inl
                                exact e'
                              · intro ex
                                apply Exists.elim ex
                                intro a ex
                                apply Exists.elim ex
                                intro b bin
                                apply Or.inr
                                exists e::a
                                exists b
                                exact ⟨by simp,by rw [←bin.2.1]; rfl,bin.2.2.1,bin.2.2.2⟩
                              · exact h


theorem accepts_iff : nfa_accepts (star_nfa t) w ↔ (w ∈ nfaLang t ∨ ∃ a b, a ≠ [] ∧ a++b=w ∧ a ∈ nfaLang t ∧ b ∈ nfaLang (star_nfa t)) := by
  apply Iff.intro
  · apply accepts_or_ex_prefix_state
  · intro h
    apply Or.elim h
    · intro win
      apply nfa_accepts_star_nfa
      exact win
    · intro ex
      apply Exists.elim ex
      intro a ex
      apply Exists.elim ex
      intro b h
      rw [←h.2.1]
      apply star_nfa_accepts_append
      · exact nfa_accepts_star_nfa _ h.2.2.1
      · exact h.2.2.2


theorem star_nfa_accepts_iff : w ∈ nfaLang (star_nfa t) ↔ w ∈ Regex.plusLang (nfaLang t) := by
  simp only [nfaLang]
  apply Iff.intro
  · intro win
    rw [Set.mem_def] at win
    rw [Set.mem_def]
    have : w ∈ nfaLang t ∨ ∃ a b, a ≠ [] ∧ a++b=w ∧ a ∈ nfaLang t ∧ b ∈ nfaLang (star_nfa t) := (accepts_iff _).mp win
    apply Or.elim this
    · intro h
      apply Regex.plusLang.empty
      apply h
    · intro h
      apply Exists.elim h
      intro a ex
      apply Exists.elim ex
      intro b h
      rw [←h.2.1]
      have : b.length < w.length := by -- make clear that the program terminates
        rw [←h.2.1]
        simp only [List.length_append,lt_add_iff_pos_left]
        apply List.length_pos_iff_ne_nil.mpr
        exact h.1
      apply Regex.plusLang.extend
      · exact h.2.2.1
      · apply star_nfa_accepts_iff.mp -- b is always smaller, so must terminate
        exact h.2.2.2
  · intro h
    induction h with
    | empty h hin => apply nfa_accepts_star_nfa t hin
    | extend a b h _ s => apply star_nfa_accepts_append t (nfa_accepts_star_nfa t h) s

termination_by star_nfa_accepts_iff => w.length

end Star

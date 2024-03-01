import Automaton.NFA.Basic
import Automaton.NFA.ToDFA
import Automaton.Regex.Basic
import Automaton.DFA.Basic
import Automaton.Language.Basic

open NFA ToDFA

variable {σ : Type _} {q : Type _} {σs : Finset σ} {qs : Finset q} (t : NFA σs qs) [DecidableEq σ] [DecidableEq q]


def starNFA_δ : qs → σs → Finset qs := fun q σ => if Finset.Nonempty (t.δ q σ ∩ t.fs) then t.δ q σ ∪ t.q₀ else t.δ q σ

def starNFA : NFA σs qs := {q₀ := t.q₀, fs := t.fs, δ := starNFA_δ t}

theorem δ_star'_union_char (q : Finset qs) : Finset.Nonempty (δ_step t q e ∩ t.fs) → δ_star' (starNFA t) q [e] = δ_star' t q [e] ∪ t.q₀ := by
  intro h
  simp only [δ_star,δ_star',δ_step]
  simp only [δ_step] at h
  simp only [starNFA,starNFA_δ]
  apply Finset.eq_iff_fa_mem.mpr
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
      · have : False := by have : ¬Finset.Nonempty (NFA.δ t b e ∩ t.fs) := by assumption
                           apply this
                           rw [Finset.Nonempty]
                           exists a
                           apply Finset.mem_inter.mpr
                           exact ⟨bin.2, ain.2⟩
        contradiction

theorem δ_star'_union_prefinal : (q : Finset qs) → (e : σs) → Finset.Nonempty (δ_step t q e ∩ t.fs) → δ_star' (starNFA t) q (e::w) = δ_star' (starNFA t) (δ_star' t q [e] ∪ t.q₀) w := by
  induction w using List.reverseRecOn with
  | H0 => intro q e ne
          simp
          apply δ_star'_union_char
          exact ne
  | H1 es e s => intro q e' ne
                 rw [←List.cons_append,←δ_star'_append_eq,s,←δ_star'_append_eq]
                 exact ne


theorem δ_subset_starNFA : t.δ s e ⊆ (starNFA t).δ s e := by
  simp only [starNFA,starNFA_δ]
  split
  · apply Finset.subset_union_left
  · rfl

theorem δ_star'_subset_starNFA : δ_star' t s w ⊆ δ_star' (starNFA t) s w  := by
  induction w using List.reverseRecOn with
  | H0 => simp
  | H1 w e ss => rw [←δ_star'_append_eq,←δ_star'_append_eq]
                 simp only [δ_star',δ_star',δ_step,Finset.biUnion_subset]
                 intro x xin
                 have h : (starNFA t).δ x e ⊆ Finset.biUnion (δ_star' (starNFA t) s w) fun n => NFA.δ (starNFA t) n e := by
                  apply Finset.subset_biUnion_of_mem (fun n => NFA.δ (starNFA t) n e)
                  apply Finset.mem_of_subset
                  apply ss
                  exact xin
                 apply Finset.instIsTransFinsetSubsetInstHasSubsetFinset.trans
                 have : t.δ x e ⊆ (starNFA t).δ x e := by apply δ_subset_starNFA
                 apply this
                 exact h

theorem nfa_accepts_starNFA : nfa_accepts t w → nfa_accepts (starNFA t) w := by
  intro h
  simp only [nfa_accepts] at h
  simp only [nfa_accepts,Finset.Nonempty]
  apply Finset.not_disjoint_iff_nonempty_inter.mp
  intro h'
  simp only [Disjoint] at h'
  simp only [Finset.Nonempty] at h
  apply Exists.elim h
  intro a ain
  have ain := Finset.mem_inter.mp ain
  have : {a} ⊆ δ_star' (starNFA t) (starNFA t).q₀ w := by apply Finset.instIsTransFinsetSubsetInstHasSubsetFinset.trans
                                                          have : {a} ⊆ δ_star' t t.q₀ w := by apply Finset.singleton_subset_iff.mpr
                                                                                              exact ain.1
                                                          apply this
                                                          apply δ_star'_subset_starNFA
  have := h' this
  simp [starNFA] at this
  apply this
  exact ain.2


theorem subset_δ_star'_subset : (s₁ s₂ : Finset qs) → s₁ ⊆ s₂ → δ_star' t s₁ w ⊆ δ_star' t s₂ w := by
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


theorem starNFA_δ_inter_Nonempty_iff : Finset.Nonempty ((starNFA t).fs ∩ (starNFA t).δ a e) ↔ Finset.Nonempty (t.fs ∩ t.δ a e) := by
  apply Iff.intro
  · intro h
    simp only [starNFA,starNFA_δ] at h
    split at h
    · rwa [Finset.inter_comm]
    · exact h
  · intro h
    simp only [starNFA,starNFA_δ]
    split
    · simp only [Finset.Nonempty]
      simp only [Finset.Nonempty] at h
      apply Exists.elim h
      intro q qin
      exists q
      apply Finset.mem_inter.mpr
      have := Finset.mem_inter.mp qin
      apply And.intro
      · exact this.1
      · apply Finset.mem_union_left
        exact this.2
    · rw [Finset.inter_comm] at h
      contradiction


theorem starNFA_accepts_start_subset : nfa_accepts (starNFA t) w → (starNFA t).q₀ ⊆ δ_star (starNFA t) w := by
  intro h
  cases List.eq_nil_or_concat w with
  | inl g => rw [g]
             simp [starNFA]
  | inr g => apply Exists.elim g
             intro l ex
             apply Exists.elim ex
             intro a eq
             rw [eq] at h
             rw [eq]
             rw [δ_star,←δ_star'_append_eq]
             simp only [δ_star',δ_step,starNFA]
             simp only [nfa_accepts,δ_star,←δ_star'_append_eq,δ_star',δ_step] at h
             rw [Finset.inter_comm,Finset.inter_biUnion] at h
             simp only [Finset.Nonempty] at h
             apply Exists.elim h
             intro q qin
             simp only [Finset.mem_biUnion] at qin
             apply Exists.elim qin
             intro q' qin'
             have  := Finset.subset_biUnion_of_mem (fun n => NFA.δ (starNFA t) n a) qin'.1
             simp only [starNFA] at this
             have ne : Finset.Nonempty ((starNFA t).fs ∩ (starNFA t).δ q' a) := by simp only [Finset.Nonempty]
                                                                                   exists q
                                                                                   exact qin'.2
             have ne' : Finset.Nonempty (t.fs ∩ NFA.δ t q' a) := (starNFA_δ_inter_Nonempty_iff t).mp ne
             simp only [starNFA_δ]
             have ss : t.q₀ ⊆ starNFA_δ t q' a := by simp only [starNFA_δ]
                                                     split
                                                     · apply Finset.subset_union_right
                                                     · rw [Finset.inter_comm] at ne'
                                                       trivial
             apply Finset.instIsTransFinsetSubsetInstHasSubsetFinset.trans
             · exact ss
             · exact this


theorem starNFA_accepts_append (a₁ : nfa_accepts (starNFA t) w₁) (a₂ : nfa_accepts (starNFA t) w₂) : nfa_accepts (starNFA t) (w₁++w₂) := by
  have := starNFA_accepts_start_subset t a₁
  simp only [nfa_accepts,δ_star]
  rw [←δ_star'_append_eq]
  simp only [nfa_accepts,δ_star,Finset.Nonempty] at a₂
  have : δ_star' (starNFA t) (starNFA t).q₀ w₂ ⊆ δ_star' (starNFA t) (δ_star' (starNFA t) (starNFA t).q₀ w₁) w₂ := by
    apply subset_δ_star'_subset
    exact this
  apply Exists.elim a₂
  intro q qin
  simp only [Finset.Nonempty]
  exists q
  rw [Finset.mem_inter] at qin
  apply Finset.mem_inter.mpr
  apply And.intro
  · apply Finset.mem_of_subset
    · apply this
    · exact qin.1
  · exact qin.2

instance instDecidableExWNeNil : Decidable (∃ a, a ∈ nfaLang t ∧ a ≠ []) := by
  have : Decidable (∃ w, DFA.dfa_accepts (nfa_to_dfa t) w ∧ w ≠ []) := by infer_instance
  match this with
  | isTrue h => apply Decidable.isTrue
                simp only [nfaLang]
                apply Exists.elim h
                intro w h
                rw [←nfa_to_dfa_eq] at h
                exists w
  | isFalse h => apply Decidable.isFalse
                 intro ex
                 simp only [nfaLang] at ex
                 apply Exists.elim ex
                 intro w hin
                 apply h
                 exists w
                 rw [←nfa_to_dfa_eq]
                 apply hin

lemma nfa_only_nil_star_only_nil : (¬∃ a, a ∈ nfaLang t ∧ a ≠ []) → (nfaLang t = ∅ ∨ nfaLang t = {[]}) := by
  intro nex
  cases Decidable.em (Finset.Nonempty (t.q₀ ∩ t.fs)) with
  | inl h => apply Or.inr
             simp only [nfaLang,nfa_accepts]
             rw [Set.eq_singleton_iff_nonempty_unique_mem]
             apply And.intro
             · apply Set.nonempty_def.mpr
               exists []
             · intro w h
               rw [not_exists] at nex
               have := nex w
               rw [not_and] at this
               simp only [nfaLang,nfa_accepts] at this
               rw [Decidable.not_not] at this
               exact this h
  | inr h => apply Or.inl
             simp only [nfaLang,nfa_accepts]
             rw [Set.eq_empty_iff_forall_not_mem]
             intro w win
             rw [not_exists] at nex
             have := nex w
             rw [Decidable.not_and] at this
             apply Or.elim this
             · intro nin
               contradiction
             · intro neq
               rw [Decidable.not_not] at neq
               apply h
               rw [Set.mem_def] at win
               rw [neq] at win
               simp only [δ_star,δ_star'] at win
               exact win

lemma δ_step_star_eq (q : Finset qs): ¬Finset.Nonempty (δ_step t q e ∩ t.fs) → δ_step (starNFA t) q e = δ_step t q e := by
  intro ne
  simp only [starNFA,starNFA_δ,δ_step]
  rw [Finset.eq_iff_fa_mem]
  intro e'
  apply Iff.intro
  · intro ein
    rw [Finset.mem_biUnion] at ein
    rw [Finset.mem_biUnion]
    apply Exists.elim ein
    intro a ain
    split at ain
    · have : False := by apply ne
                         simp only [δ_step,Finset.biUnion_inter,Finset.Nonempty]
                         have : Finset.Nonempty (NFA.δ t a e ∩ t.fs) := by assumption
                         rw [Finset.Nonempty] at this
                         apply Exists.elim this
                         intro x xin
                         exists x
                         rw [Finset.mem_biUnion]
                         exists a
                         exact ⟨ain.1,xin⟩
      contradiction
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


theorem starNFA_split_state : (q : Finset qs) → Finset.Nonempty (δ_star' (starNFA t) q w ∩ (starNFA t).fs) →
  (Finset.Nonempty (δ_star' t q w ∩ t.fs) ∨ ∃ a b, a ≠ [] ∧ a++b=w ∧ Finset.Nonempty (δ_star' t q a ∩ t.fs) ∧ b ∈ nfaLang (starNFA t)) := by
  induction w with
  | nil=> simp only [nfaLang,nfa_accepts,δ_star,δ_star',δ_step]
          intro h
          apply Or.inl
  | cons e es s => intro q acc
                   simp only [nfaLang,Set.mem_def,nfa_accepts,δ_star] at acc
                   simp only [nfaLang,Set.mem_def,nfa_accepts,δ_star]
                   cases Decidable.em (Finset.Nonempty (δ_step t q e ∩ t.fs)) with
                   | inl h => have eq : δ_star' (starNFA t) q [e] = δ_star' (starNFA t) (δ_star' t q [e] ∪ t.q₀) [] := δ_star'_union_prefinal t q e h
                              simp only [δ_star'] at eq
                              simp only [δ_star']
                              simp only [δ_star'] at acc
                              have : (starNFA t).q₀ = t.q₀ := by simp [starNFA]
                              rw [eq] at acc
                              rw [δ_star'_union] at acc
                              simp only [Finset.Nonempty] at acc
                              apply Exists.elim acc
                              intro x xin
                              rw [Finset.mem_inter,Finset.mem_union] at xin
                              apply Or.elim xin.1
                              · intro xins
                                have s' := s (δ_step t q e)
                                have : Finset.Nonempty (δ_star' (starNFA t) (δ_step t q e) es ∩ (starNFA t).fs) := by
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
                                  simp
                                  use bin.2.1
                                  apply And.intro
                                  · exact bin.2.2.1
                                  · apply bin.2.2.2
                              · intro xins
                                apply Or.inr
                                exists [e]
                                exists es
                                simp
                                apply And.intro
                                · apply h
                                · simp only [Finset.Nonempty]
                                  exists x
                                  rw [Finset.mem_inter]
                                  exact ⟨xins,xin.2⟩
                   | inr h => simp only [δ_star'] at acc
                              have := s ((δ_step (starNFA t) q e)) acc
                              apply Or.elim this
                              · intro e'
                                apply Or.inl
                                simp only [δ_star']
                                rw [δ_step_star_eq] at e'
                                exact e'
                                exact h
                              · intro ex
                                apply Exists.elim ex
                                intro a ex
                                apply Exists.elim ex
                                intro b bin
                                apply Or.inr
                                exists e::a
                                exists b
                                simp
                                use bin.2.1
                                apply And.intro
                                · rw [δ_step_star_eq] at bin
                                  simp only [δ_step] at bin
                                  exact bin.2.2.1
                                  exact h
                                · simp only [nfaLang,nfa_accepts,Set.mem_def] at bin
                                  exact bin.2.2.2


theorem starNfa_split : w ∈ nfaLang (starNFA t) → (w ∈ nfaLang t ∨ ∃ a b, a ≠ [] ∧ a++b=w ∧ a ∈ nfaLang t ∧ b ∈ nfaLang (starNFA t)) := by
  simp only [nfaLang,nfa_accepts]
  apply starNFA_split_state


theorem no_accept_nfa_starNFA_eq : (¬∃ e es, Finset.Nonempty (δ_star t (e::es) ∩ t.fs)) → ∀ w, (δ_star (starNFA t) w) = δ_star t w := by
  intro h' w
  have nex2 : ¬∃ e es, Finset.Nonempty (δ_star t (List.concat es e) ∩ t.fs) := by
    intro ex
    apply h'
    apply Exists.elim ex
    intro e ex
    apply Exists.elim ex
    intro es h
    have : ∃ b L, List.concat es e = b :: L := List.exists_cons_of_ne_nil (by simp)
    apply Exists.elim this
    intro b ex
    apply Exists.elim ex
    intro L h
    exists b
    exists L
    rw [←h]
    trivial
  have eqδ : ∀ t : (NFA σs qs),∀ w, δ_star' t t.q₀ w = δ_star t w := by
    intro t w
    simp only [δ_star]
  simp only [starNFA,starNFA_δ]
  induction w using List.reverseRecOn with
  | H0 => simp
  | H1 es e s => simp only [δ_star,←δ_star'_append_eq]
                 simp only [δ_star',δ_step]
                 rw [eqδ,s,Finset.eq_iff_fa_mem]
                 intro e'
                 rw [Finset.mem_biUnion]
                 apply Iff.intro
                 · intro ein'
                   apply Exists.elim ein'
                   intro q qin
                   rw [not_exists] at nex2
                   have := nex2 e
                   rw [not_exists] at this
                   have not := this es
                   rw [List.concat_eq_append] at not
                   simp only [δ_star] at not
                   rw [←δ_star'_append_eq] at not
                   simp only [δ_star'] at not
                   split at qin
                   · have : False := by
                            apply not
                            have : Finset.Nonempty (NFA.δ t q e ∩ t.fs) := by assumption
                            rw [Finset.Nonempty] at this
                            apply Exists.elim this
                            intro q' qin'
                            simp only [Finset.Nonempty,δ_step]
                            rw [Finset.biUnion_inter]
                            exists q'
                            rw [Finset.mem_biUnion]
                            exists q
                            use qin.1
                            exact qin'
                     trivial
                   · rw [Finset.mem_biUnion]
                     exists q
                 · intro ein
                   rw [Finset.mem_biUnion] at ein
                   apply Exists.elim ein
                   intro e ein
                   exists e
                   use ein.1
                   split
                   · apply Finset.mem_union_left
                     exact ein.2
                   · exact ein.2

theorem starNFA_accepts_plusLang : w ∈ nfaLang (starNFA t) ↔ w ∈ Regex.plusLang (nfaLang t) := by
  simp only [nfaLang]
  apply Iff.intro
  · intro win
    rw [Set.mem_def] at win
    rw [Set.mem_def]
    have : w ∈ nfaLang t ∨ ∃ a b, a ≠ [] ∧ a++b=w ∧ a ∈ nfaLang t ∧ b ∈ nfaLang (starNFA t) := starNfa_split t win
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
      have : b.length < w.length := by rw [←h.2.1] -- make clear that the program terminates
                                       simp only [List.length_append,lt_add_iff_pos_left]
                                       apply List.length_pos_iff_ne_nil.mpr
                                       exact h.1
      apply Regex.plusLang.extend
      · exact h.2.2.1
      · apply starNFA_accepts_plusLang.mp -- b is always smaller, so must terminate
        exact h.2.2.2
  · intro h
    induction h with
    | empty h hin => apply nfa_accepts_starNFA t hin
    | extend a b h _ s => apply starNFA_accepts_append t (nfa_accepts_starNFA t h) s

termination_by starNFA_accepts_plusLang => w.length

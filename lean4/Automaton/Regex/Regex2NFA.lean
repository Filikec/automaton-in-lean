import Automaton.Regex.Star
import Automaton.Regex.Zero
import Automaton.Regex.Append
import Automaton.Regex.Plus
import Automaton.Regex.Char
import Automaton.Regex.Empty
import Automaton.Regex.Basic

namespace ToNFA

open NFA Regex

variable {σ : Type _} {σs : Finset σ} [DecidableEq σ]


def regex2NFA : Regex σs → NFA σs
  | Regex.zero => Zero.zeroNfa
  | Regex.epsilon => Empty.empty
  | Regex.char a => Char.char a
  | Regex.plus a b => Plus.plus_nfa (regex2NFA a) (regex2NFA b)
  | Regex.append a b => Append.append_nfa (regex2NFA a) (regex2NFA b)
  | Regex.star a => Plus.plus_nfa (Star.star_nfa (regex2NFA a)) (Empty.empty)


mutual
theorem star_to_regex (s : w ∈ nfaLang (regex2NFA a) → w ∈ RegexLan σs a) (h : w ∈ nfaLang (Star.star_nfa (regex2NFA a))) : w ∈ RegexLan σs (Regex.star a) := by
  simp only [nfaLang,Set.mem_def] at h
  rw [Star.accepts_iff] at h
  apply Or.elim h
  · intro h
    have : w = w ++ [] := by simp
    rw [this]
    simp only [RegexLan]
    apply starLang.extend
    · exact s h
    · apply starLang.empty
  · intro ex
    apply Exists.elim ex
    intro a' ex
    apply Exists.elim ex
    intro b h
    rw [←h.2.1]
    apply starLang.extend
    · match b with
      | [] => rw [List.append_nil] at h
              rw [h.2.1]
              rw [h.2.1] at h
              apply s h.2.2.1
      | b::bs => have : a'.length < w.length := by rw [←h.2.1]; simp
                 apply regex2NFA_eq.mp h.2.2.1
    · have : List.length b < List.length w := by
        rw [←h.2.1]
        simp only [List.length_append,lt_add_iff_pos_left]
        apply List.length_pos_iff_ne_nil.mpr
        exact h.1
      rw [←h.2.1] at s
      apply star_to_regex
      · intro bin
        apply regex2NFA_eq.mp bin
      · exact h.2.2.2

theorem regex_to_star (s : w ∈ RegexLan σs a → w ∈ nfaLang (regex2NFA a)) (h : w ∈ RegexLan σs (Regex.star a)) : w ∈ nfaLang (regex2NFA (Regex.star a)) := by
  simp only [RegexLan] at h
  rw [mem_starLang_iff] at h
  simp only [nfaLang,regex2NFA,Set.mem_def,Plus.accepts_iff]
  apply Or.elim h
  · intro eq
    rw [eq]
    apply Or.inr
    rw [Empty.accepts_iff]
  · intro ex
    apply Exists.elim ex
    intro a' ex
    apply Exists.elim ex
    intro b h
    apply Or.inl
    rw [Star.accepts_iff]
    match b with
    | [] => rw [List.append_nil] at h
            rw [h.2.1] at h
            apply Or.inl
            apply s
            exact h.2.2.1
    | b::bs => have : (b::bs).length < w.length := by
                rw [←h.2.1]
                simp only [List.length_append,lt_add_iff_pos_left]
                apply List.length_pos_iff_ne_nil.mpr
                exact h.1
               have im : b::bs ∈ RegexLan σs a → b::bs ∈ nfaLang (regex2NFA a) := by intro bin; exact regex2NFA_eq.mpr bin
               have := regex_to_star im h.2.2.2
               simp only [regex2NFA,nfaLang,Set.mem_def,Plus.accepts_iff] at this
               apply Or.elim this
               · intro h'
                 apply Or.inr
                 have : a'.length < w.length := by rw [←h.2.1]; simp
                 exists a'
                 exists b::bs
                 use h.1, h.2.1, regex2NFA_eq.mpr h.2.2.1
                 simp only [nfaLang,Set.mem_def]
                 exact h'
               · intro h'
                 rw [Empty.accepts_iff] at h'
                 contradiction




theorem regex2NFA_eq  : w ∈ nfaLang (regex2NFA r) ↔ w ∈ RegexLan σs r := by
  apply Iff.intro
  · intro h
    induction r with
    | zero => simp only [regex2NFA,nfaLang,Zero.not_accepts] at h; simp only [RegexLan]; apply h
    | epsilon => simp only [regex2NFA,nfaLang,Empty.accepts_iff] at h; simp only [RegexLan]; apply h
    | char a => simp only [regex2NFA,nfaLang,Char.accepts_iff] at h; simp only [RegexLan]; apply h
    | plus a b s₁ s₂ => simp only [regex2NFA,nfaLang,regex2NFA,Plus.accepts_iff,Set.mem_def] at h
                        simp only [RegexLan,Set.mem_union]
                        apply Or.elim h
                        · intro h
                          apply Or.inl
                          apply s₁ h
                        intro h
                        apply Or.inr
                        apply s₂ h
    | append a b s₁ s₂ => simp only [regex2NFA,nfaLang,Append.accepts_iff,Set.mem_def] at h
                          simp only [nfaLang,Set.mem_def] at s₁
                          simp only [nfaLang,Set.mem_def] at s₂
                          simp only [RegexLan,Set.mem_def,setOf]
                          apply Exists.elim h
                          intro a ex
                          apply Exists.elim ex
                          intro b h
                          match w with
                          | [] => have : a = [] ∧ b = [] := by apply List.append_eq_nil.mp h.2.2
                                  rw [this.1,this.2] at h
                                  exists []
                                  exists []
                                  use s₁ h.1, s₂ h.2.1
                                  rfl
                          | w::ws => match b with
                                     | [] => rw [List.append_nil] at h
                                             rw [←h.2.2]
                                             exists a
                                             exists []
                                             rw [h.2.2]
                                             rw [h.2.2] at h
                                             use s₁ h.1
                                             use regex2NFA_eq.mp h.2.1
                                             simp
                                     | b::bs => match a with
                                                | [] => rw [List.nil_append] at h
                                                        rw [←h.2.2]
                                                        exists []
                                                        exists b::bs
                                                        rw [h.2.2]
                                                        rw [h.2.2] at h
                                                        use regex2NFA_eq.mp h.1
                                                        use s₂ h.2.1
                                                        simp
                                                | a::as => exists a::as
                                                           exists b::bs
                                                           have eq : List.length (a::as++b::bs) = List.length (w::ws) := by rw [h.2.2]
                                                           have : List.length (a::as) < List.length (w::ws) := by rw [List.length_append] at eq
                                                                                                                  rw [←eq]
                                                                                                                  simp
                                                           have : List.length (b::bs) < List.length (w::ws) := by rw [List.length_append] at eq
                                                                                                                  rw [←eq]
                                                                                                                  simp
                                                           use regex2NFA_eq.mp h.1
                                                           use regex2NFA_eq.mp h.2.1
                                                           rw [←h.2.2]
    | star a s => simp only [regex2NFA,nfaLang,regex2NFA,Plus.accepts_iff,Set.mem_def] at h
                  simp only [RegexLan]
                  apply Or.elim h
                  · intro h
                    rw [Star.accepts_iff] at h
                    apply Or.elim h
                    · intro win
                      have : w = w ++ [] := by simp
                      rw [this]
                      apply starLang.extend
                      · apply s win
                      · apply starLang.empty
                    · intro ex
                      apply Exists.elim ex
                      intro a ex
                      apply Exists.elim ex
                      intro b h
                      rw [←h.2.1]
                      have : b.length < w.length := by
                              rw [←h.2.1]
                              simp only [List.length_append,lt_add_iff_pos_left]
                              apply List.length_pos_iff_ne_nil.mpr
                              exact h.1
                      apply starLang.extend
                      · match b with
                        | [] => rw [List.append_nil] at h
                                rw [h.2.1]
                                rw [h.2.1] at h
                                apply s h.2.2.1
                        | b::bs => have : a.length < w.length := by rw [←h.2.1]; simp
                                   apply regex2NFA_eq.mp h.2.2.1
                      · apply star_to_regex
                        · intro bin
                          apply regex2NFA_eq.mp bin
                        · exact h.2.2.2
                  · intro h
                    rw [Empty.accepts_iff] at h
                    rw [h]
                    apply starLang.empty
  · intro h
    induction r with
    | zero => simp only [RegexLan] at h; simp only [regex2NFA,nfaLang,Zero.not_accepts,Set.mem_def]; apply h
    | epsilon => simp only [regex2NFA,nfaLang,Empty.accepts_iff]; apply h
    | char a => simp only [regex2NFA,nfaLang,Char.accepts_iff]; apply h
    | plus a b s₁ s₂ => simp only [regex2NFA,nfaLang,regex2NFA,Plus.accepts_iff,Set.mem_def]
                        simp only [RegexLan,Set.mem_union] at h
                        apply Or.elim h
                        · intro h
                          apply Or.inl
                          apply s₁ h
                        intro h
                        apply Or.inr
                        apply s₂ h
    | append a b s₁ s₂ => simp only [RegexLan,Set.mem_def,setOf] at h
                          simp only [regex2NFA,nfaLang,Set.mem_def,Append.accepts_iff]
                          apply Exists.elim h
                          intro a ex
                          apply Exists.elim ex
                          intro b h
                          exists a
                          exists b
                          match w with
                          | [] => have : a = [] ∧ b = [] := List.append_eq_nil.mp (Eq.symm h.2.2)
                                  rw [this.1,this.2]
                                  rw [this.1,this.2] at h
                                  use s₁ h.1, s₂ h.2.1
                                  rfl
                          | w::ws => match b with
                                     | [] => rw [List.append_nil] at h
                                             rw [←h.2.2]
                                             rw [←h.2.2] at h
                                             use s₁ h.1
                                             use regex2NFA_eq.mpr h.2.1
                                             simp
                                     | b::bs => match a with
                                                | [] => rw [List.nil_append] at h
                                                        rw [←h.2.2]
                                                        rw [←h.2.2] at h
                                                        use regex2NFA_eq.mpr h.1
                                                        use s₂ h.2.1
                                                        simp
                                                | a::as => have eq : List.length (a::as++b::bs) = List.length (w::ws) := by rw [h.2.2]
                                                           have : List.length (a::as) < List.length (w::ws) := by rw [List.length_append] at eq
                                                                                                                  rw [←eq]
                                                                                                                  simp
                                                           have : List.length (b::bs) < List.length (w::ws) := by rw [List.length_append] at eq
                                                                                                                  rw [←eq]
                                                                                                                  simp
                                                           use regex2NFA_eq.mpr h.1
                                                           use regex2NFA_eq.mpr h.2.1
                                                           rw [←h.2.2]
    | star a s => simp only [RegexLan] at h
                  rw [mem_starLang_iff] at h
                  simp only [nfaLang,regex2NFA,Set.mem_def,Plus.accepts_iff]
                  apply Or.elim h
                  · intro eq
                    rw [eq]
                    apply Or.inr
                    rw [Empty.accepts_iff]
                  · intro ex
                    apply Exists.elim ex
                    intro a' ex
                    apply Exists.elim ex
                    intro b h
                    apply Or.inl
                    rw [Star.accepts_iff]
                    match b with
                    | [] => rw [List.append_nil] at h
                            rw [h.2.1] at h
                            apply Or.inl
                            apply s
                            exact h.2.2.1
                    | b::bs => apply Or.inr
                               have : (b::bs).length < w.length := by
                                rw [←h.2.1]
                                simp only [List.length_append,lt_add_iff_pos_left]
                                apply List.length_pos_iff_ne_nil.mpr
                                exact h.1
                               have : a'.length < w.length := by rw [←h.2.1]; simp
                               exists a'
                               exists b::bs
                               use h.1, h.2.1, regex2NFA_eq.mpr h.2.2.1
                               have : (b::bs ∈ RegexLan σs a → b::bs ∈ nfaLang (regex2NFA a)) := by intro bin
                                                                                                    apply regex2NFA_eq.mpr bin
                               have := regex_to_star this h.2.2.2
                               simp only [regex2NFA,nfaLang,Set.mem_def] at this
                               rw [Plus.accepts_iff] at this
                               apply Or.elim this
                               · intro h'
                                 simp only [regex2NFA,nfaLang,Set.mem_def]
                                 exact h'
                               · intro h'
                                 rw [Empty.accepts_iff] at h'
                                 contradiction


end
termination_by star_to_regex => w.length
               regex2NFA_eq => w.length
               regex_to_star => w.length

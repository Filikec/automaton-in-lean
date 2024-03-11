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
                    have : w ∈ nfaLang (Star.star_nfa (regex2NFA a)) := by simp only [nfaLang,Set.mem_def]; assumption
                    rw [Star.accepts_iff] at this
                    apply Or.elim this
                    · intro h
                      have : w = w ++ [] := by simp
                      rw [this]
                      apply starLang.extend
                      · apply s h
                      · apply starLang.empty
                    · intro ex
                      apply Exists.elim ex
                      intro a ex
                      apply Exists.elim ex
                      intro b h
                      rw [←h.2.1]
                      apply starLang.extend
                      · apply regex2NFA_eq.mp h.2.2.1
                      · have : b = b ++ [] := by simp
                        rw [this]
                        apply starLang.extend
                        · sorry
                        · apply starLang.empty
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
    | append a b s₁ s₂ => sorry
    | star a s => sorry

termination_by regex2NFA_eq => w.length;

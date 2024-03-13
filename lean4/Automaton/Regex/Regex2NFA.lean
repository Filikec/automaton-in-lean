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


theorem star_to_regex (s₁ : w ∈ nfaLang (regex2NFA a) → w ∈ RegexLan σs a)
  (s₂ : ∀ w', w'.length < w.length → w' ∈ nfaLang (regex2NFA a) → w' ∈ RegexLan σs a)
  (h : w ∈ nfaLang (regex2NFA (Regex.star a))) : w ∈ RegexLan σs (Regex.star a) := by
  simp only [nfaLang,Set.mem_def,regex2NFA] at h
  rw [Plus.accepts_iff,Star.accepts_iff] at h
  apply Or.elim h
  · intro h
    apply Or.elim h
    · intro h
      have : w = w ++ [] := by simp
      rw [this]
      simp only [RegexLan]
      apply starLang.extend
      · exact s₁  h
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
                apply s₁ h.2.2.1
        | b::bs => have : a'.length < w.length := by rw [←h.2.1]; simp
                   apply s₂ _ this h.2.2.1
      · have : List.length b < List.length w := by
          rw [←h.2.1]
          simp only [List.length_append,lt_add_iff_pos_left]
          apply List.length_pos_iff_ne_nil.mpr
          exact h.1
        apply star_to_regex (s₂ _ this)
        · intro w' lt w'in
          have : w'.length < w.length := by apply Nat.lt_trans lt this
          exact s₂ _ this w'in
        · simp only [regex2NFA,nfaLang,Set.mem_def,Plus.accepts_iff]
          apply Or.inl
          exact h.2.2.2
  · intro em
    rw [Empty.accepts_iff] at em
    rw [em]
    simp only [RegexLan]
    apply starLang.empty
termination_by star_to_regex => w.length

theorem regex_to_star (s₁ : w ∈ RegexLan σs a → w ∈ nfaLang (regex2NFA a))
  (s₂ : ∀ w', w'.length < w.length → w' ∈ RegexLan σs a → w' ∈ nfaLang (regex2NFA a))
  (h : w ∈ RegexLan σs (Regex.star a)) : w ∈ nfaLang (regex2NFA (Regex.star a)) := by
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
            apply s₁
            exact h.2.2.1
    | b::bs => have lt₁ : (b::bs).length < w.length := by
                rw [←h.2.1]
                simp only [List.length_append,lt_add_iff_pos_left]
                apply List.length_pos_iff_ne_nil.mpr
                exact h.1
               have lt₂ : a'.length < w.length := by rw [←h.2.1]; simp
               simp only [nfaLang,Set.mem_def] at s₂
               apply Or.inr
               exists a'
               exists b::bs
               use h.1, h.2.1, s₂ a' lt₂ h.2.2.1
               have bin : b::bs ∈ RegexLan σs (Regex.star a) := by simp only [RegexLan]; exact h.2.2.2
               have fa : ∀ w', w'.length < (b::bs).length → RegexLan σs a w' → nfa_accepts (regex2NFA a) w' := by
                intro w' lt r
                apply s₂ _ (Nat.lt_trans lt lt₁) r
               have := regex_to_star (s₂ _ lt₁) fa bin
               simp only [regex2NFA,nfaLang,Set.mem_def] at this
               rw [Plus.accepts_iff] at this
               apply Or.elim this
               · intro bin
                 apply bin
               · intro em
                 rw [Empty.accepts_iff] at em
                 contradiction
termination_by regex_to_star => w.length

theorem append_to_regex (s₁: w ∈ nfaLang (regex2NFA a) → w ∈ RegexLan σs a)
  (s₂: w ∈ nfaLang (regex2NFA b) → w ∈ RegexLan σs b)
  (h: w ∈ nfaLang (regex2NFA (Regex.append a b)))
  (fa₁: ∀ (w' : List { x // x ∈ σs }), List.length w' < List.length w → w' ∈ nfaLang (regex2NFA a) → w' ∈ RegexLan σs a)
  (fa₂: ∀ (w' : List { x // x ∈ σs }), List.length w' < List.length w → w' ∈ nfaLang (regex2NFA b) → w' ∈ RegexLan σs b) : w ∈ RegexLan σs (Regex.append a b) := by
  simp only [regex2NFA,nfaLang,Append.accepts_iff,Set.mem_def] at h
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
                      use fa₂ _ (by simp) h.2.1
                      simp
              | b::bs => match a with
                        | [] => rw [List.nil_append] at h
                                rw [←h.2.2]
                                exists []
                                exists b::bs
                                rw [h.2.2]
                                rw [h.2.2] at h
                                use fa₁ _ (by simp) h.1
                                use s₂ h.2.1
                                simp
                        | a::as => exists a::as
                                   exists b::bs
                                   have eq : List.length (a::as++b::bs) = List.length (w::ws) := by rw [h.2.2]
                                   have lt₁ : List.length (a::as) < List.length (w::ws) := by rw [List.length_append] at eq
                                                                                              rw [←eq]
                                                                                              simp
                                   have lt₂ : List.length (b::bs) < List.length (w::ws) := by rw [List.length_append] at eq
                                                                                              rw [←eq]
                                                                                              simp
                                   use fa₁ _ lt₁ h.1
                                   use fa₂ _ lt₂ h.2.1
                                   rw [←h.2.2]

theorem regex_to_append (s₁: w ∈ RegexLan σs a → w ∈ nfaLang (regex2NFA a) )
  (s₂: w ∈ RegexLan σs b → w ∈ nfaLang (regex2NFA b))
  (h: w ∈ RegexLan σs (Regex.append a b))
  (fa₁: ∀ (w' : List { x // x ∈ σs }), List.length w' < List.length w → w' ∈ RegexLan σs a → w' ∈ nfaLang (regex2NFA a))
  (fa₂: ∀ (w' : List { x // x ∈ σs }), List.length w' < List.length w → w' ∈ RegexLan σs b → w' ∈ nfaLang (regex2NFA b)) : w ∈ nfaLang (regex2NFA (Regex.append a b)) := by
  simp only [RegexLan,Set.mem_def,setOf] at h
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
                      use fa₂ _ (by simp) h.2.1
                      simp
              | b::bs => match a with
                        | [] => rw [List.nil_append] at h
                                rw [←h.2.2]
                                rw [←h.2.2] at h
                                use fa₁ _ (by simp) h.1
                                use s₂ h.2.1
                                simp
                        | a::as => have eq : List.length (a::as++b::bs) = List.length (w::ws) := by rw [h.2.2]
                                   have lt₁ : List.length (a::as) < List.length (w::ws) := by rw [List.length_append] at eq
                                                                                              rw [←eq]
                                                                                              simp
                                   have lt₂ : List.length (b::bs) < List.length (w::ws) := by rw [List.length_append] at eq
                                                                                              rw [←eq]
                                                                                              simp
                                   use fa₁ _ lt₁ h.1
                                   use fa₂ _ lt₂ h.2.1
                                   rw [←h.2.2]

theorem nfa2regex : w ∈ nfaLang (regex2NFA r) → w ∈ RegexLan σs r := by
  intro h
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
  | append a b s₁ s₂ => have fa₁ : ∀ w', List.length w' < List.length w → w' ∈ nfaLang (regex2NFA a) → w' ∈ RegexLan σs a := by
                          intro w' _ w'in
                          exact nfa2regex w'in
                        have fa₂ : ∀ w', List.length w' < List.length w → w' ∈ nfaLang (regex2NFA b) → w' ∈ RegexLan σs b := by
                          intro w' _ w'in
                          exact nfa2regex w'in
                        apply append_to_regex s₁ s₂ h fa₁ fa₂
  | star a s => have fa : ∀ w', List.length w' < List.length w → w' ∈ nfaLang (regex2NFA a) → w' ∈ RegexLan σs a := by
                  intro w' _ w'in
                  exact nfa2regex w'in
                apply star_to_regex s fa h
termination_by nfa2regex => w.length

theorem regex2nfa : w ∈ RegexLan σs r → w ∈ nfaLang (regex2NFA r) := by
  intro h
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
  | append a b s₁ s₂ => have fa₁ : ∀ w', List.length w' < List.length w → w' ∈ RegexLan σs a → w' ∈ nfaLang (regex2NFA a):= by
                          intro w' _ w'in
                          exact regex2nfa w'in
                        have fa₂ : ∀ w', List.length w' < List.length w →  w' ∈ RegexLan σs b → w' ∈ nfaLang (regex2NFA b) := by
                          intro w' _ w'in
                          exact regex2nfa w'in
                        exact regex_to_append s₁ s₂ h fa₁ fa₂
  | star a s => have fa : ∀ w', List.length w' < List.length w → w' ∈ RegexLan σs a → w' ∈ nfaLang (regex2NFA a) := by
                  intro w' _ w'in
                  exact regex2nfa w'in
                apply regex_to_star s fa h
termination_by regex2nfa => w.length

theorem regex2NFA_eq_regex : nfaLang (regex2NFA r) = RegexLan σs r := by
  rw [Set.ext_iff]
  intro x
  apply Iff.intro
  · apply nfa2regex
  · apply regex2nfa

import Mathlib.Data.Fintype.Card
import Automaton.DFA.Basic
import Automaton.Language.Basic

open DFA

namespace PumpingLemma

variable {σ : Type _}  {σs : Finset σ}  [DecidableEq σ] (dfa : DFA σs)

-- based on proof in mathlib4 Computability/DFA

-- if a word has more characters than number of states in DFA and is accepted, at least one state must be repeated in its δ*
theorem word_cycle {s t : dfa.qs} (hlen : dfa.qs.card ≤ w.length) (hx : δ_star' dfa s w = t) :
    ∃ q a b c, w = a ++ b ++ c ∧ a.length + b.length ≤ dfa.qs.card ∧ b ≠ [] ∧ δ_star' dfa s a = q ∧ δ_star' dfa q b = q ∧ δ_star' dfa q c = t := by
  obtain ⟨n, m, hneq, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun n : Fin (Fintype.card dfa.qs + 1) => δ_star' dfa s (w.take n)) (by simp)
  wlog hle : (n : ℕ) ≤ m
  · exact this _ hlen hx _ _ hneq.symm heq.symm (le_of_not_le hle)
  have hm : (m : ℕ) ≤ Fintype.card dfa.qs := Fin.is_le m
  have cardEq : Fintype.card {x // x ∈ dfa.qs} = Finset.card dfa.qs := by simp
  rw [←cardEq] at hlen
  refine'
    ⟨δ_star' dfa s ((w.take m).take n), (w.take m).take n, (w.take m).drop n, w.drop m, _, _, _, by rfl, _⟩
  · rw [List.take_append_drop, List.take_append_drop]
  · simp only [List.length_drop, List.length_take]
    rw [min_eq_left (hm.trans _), min_eq_left hle, add_tsub_cancel_of_le hle]
    · rw [←cardEq]
      exact hm
    · exact hlen
  · intro h
    have hlen' := congr_arg List.length h
    simp only [List.length_drop, List.length, List.length_take] at hlen'
    rw [min_eq_left, tsub_eq_zero_iff_le] at hlen'
    · apply hneq
      apply le_antisymm
      assumption'
    exact hm.trans hlen
  have hq : δ_star' dfa (δ_star' dfa s ((w.take m).take n)) ((w.take m).drop n) = δ_star' dfa s ((w.take m).take n) := by
    rw [List.take_take, min_eq_left hle, ←δ_star'_append_eq, heq, ← min_eq_left hle, ←List.take_take, min_eq_left hle, List.take_append_drop]
  use hq
  rwa [← hq, ← δ_star'_append_eq, ← δ_star'_append_eq, ← List.append_assoc, List.take_append_drop, List.take_append_drop]



-- Any word accepted by a dfa can be broken into three parts and the middle part can be repeated any number of time
-- and each time it will remain in the language. tldr; there is a cycle
theorem ex_split (hlen : dfa.qs.card ≤ w.length) (hw : w ∈ dfaLang dfa) :
    ∃ a b c, w = a ++ b ++ c ∧ a.length + b.length ≤ dfa.qs.card ∧ b ≠ [] ∧ ∀ n, (a ++ power b n ++ c) ∈ dfaLang dfa := by
  obtain ⟨_, a, b, c, hx, hlen, hnil, rfl, hb, hc⟩ := word_cycle dfa hlen rfl
  use a, b, c, hx, hlen, hnil
  intro n
  rw [Set.mem_def]
  simp only [dfaLang,dfa_accepts]
  induction n with
  | zero => simp only [δ_star]
            rw [δ_star'_append_eq,δ_star'_append_eq]
            simp only [power,δ_star']
            rw [hc]
            assumption
  | succ n s => simp only [power,δ_star,δ_star'_append_eq]
                simp only [δ_star,δ_star'_append_eq] at s
                rw [hb]
                exact s

theorem pumping_lemma : ∃ n, ∀ w ∈ dfaLang dfa, n ≤ w.length →
  ∃ a b c, w = a ++ b ++ c ∧ a.length + b.length ≤ n ∧ b ≠ [] ∧ ∀ x, (a ++ power b x ++ c) ∈ dfaLang dfa := by
    exists dfa.qs.card
    intro w win lt
    apply ex_split
    · exact lt
    · exact win

end PumpingLemma

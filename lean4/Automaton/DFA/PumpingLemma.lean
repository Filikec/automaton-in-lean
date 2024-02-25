import Automaton.DFA.Basic
import Mathlib.Data.Fintype.Card

namespace DFA

variable {σ : Type _} {q : Type _}  {σs : Finset σ} {qs : Finset q} [DecidableEq σ] [DecidableEq q] (dfa : DFA σs qs)

-- based on proof in mathlib4 Computability/DFA

-- if a word has more characters than number of states in DFA, at least one state must be repeated
theorem word_cycle {w : word σs} {s t : qs} (hlen : qs.card ≤ w.length) (hx : δ_star' dfa s w = t) :
    ∃ q a b c, w = a ++ b ++ c ∧ a.length + b.length ≤ qs.card ∧ b ≠ [] ∧ δ_star' dfa s a = q ∧ δ_star' dfa q b = q ∧ δ_star' dfa q c = t := by
  have ⟨n, m, hneq, heq⟩  := Fintype.exists_ne_map_eq_of_card_lt (fun n : Fin (Fintype.card qs + 1) => δ_star' dfa s (w.take n)) (by simp)
  wlog hle : (n : ℕ) ≤ m
  · exact this _ hlen hx _ _ hneq.symm heq.symm (le_of_not_le hle)
  have hm : (m : ℕ) ≤ Fintype.card qs := Fin.is_le m
  have cardEq : Fintype.card {x // x ∈ qs} = Finset.card qs := by simp
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


def listPower (l : List α) : ℕ → List α
  | 0  => []
  | n+1  => l ++ listPower l n

-- Any word accepted by a dfa can be broken into three parts and the middle part can be repeated any number of time
-- and each time it will remain in the language. tldr; there is a cycle
theorem pumping_lemma {w : word σs} (hlen : qs.card ≤ w.length) (hw : w ∈ dfaLang dfa) :
    ∃ a b c, w = a ++ b ++ c ∧ a.length + b.length ≤ qs.card ∧ b ≠ [] ∧ ∀ n, (a ++ listPower b n ++ c) ∈ dfaLang dfa := by
  obtain ⟨_, a, b, c, hx, hlen, hnil, rfl, hb, hc⟩ := word_cycle dfa hlen rfl
  use a, b, c, hx, hlen, hnil
  intro n
  rw [Set.mem_def]
  simp only [dfaLang,dfa_accepts]
  induction n with
  | zero => simp only [δ_star]
            rw [δ_star'_append_eq,δ_star'_append_eq]
            simp only [listPower,δ_star']
            rw [hc]
            assumption
  | succ n s => simp only [listPower,δ_star,δ_star'_append_eq]
                simp only [δ_star,δ_star'_append_eq] at s
                rw [hb]
                exact s


end DFA

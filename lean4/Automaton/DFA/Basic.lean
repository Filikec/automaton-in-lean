import Mathlib.Data.Finset.Basic
import Mathlib.Data.FinEnum
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.List
import Mathlib.Data.Vector.Basic
import Mathlib.Data.List.Card
import Automaton.Finset.Basic
import Automaton.Fintype.List
import Automaton.Language.Basic



/-!
  This file contains the definition of a DFA as well as a few fundamental operations it can do
  * `δ_star` and `accepts` functions.
  * Asserts the decidability of the language of DFA
  * Provides a definition for equality of DFA and proves basic properties about the equality
    * Two DFAs are equal, if they accept the same language
  * Provides an inductive definition of `reachable` - all states that can be reached from a state
  * Contains some lemmas and theorems that provide an easier way to prove things about accepted langs
  * Main theorems about languages : `accepts_prefix_iff` , `accepts_suffix_iff`


  * Also includes prove that `reachable` is Decidable by defining `is_path`
-/

namespace DFA


structure DFA (σs : Finset σ) where
  q : Type _
  qs : Finset q    -- set of states
  q₀ : qs          -- initial state
  fs : Finset qs   -- accepting states
  δ : qs → σs → qs -- transition function
  [d₁ : DecidableEq σ]
  [d₂ : DecidableEq q]


variable {σ : Type _} {q : Type _}  {σs : Finset σ}  [DecidableEq σ] [DecidableEq q] (r s t : DFA σs)

instance decEqQ : DecidableEq t.q := t.d₂
instance decEqσ : DecidableEq σ := t.d₁

-- ToString
def toString [ToString σ] [ToString t.q] [fσ : FinEnum σ] [fq : FinEnum t.q] : String := by
    have s : List String := (fσ.toList).map ToString.toString
    have q : String := ToString.toString t.q₀
    have qss : List String :=  (fq.toList).map ToString.toString
    have fs : List String := ((fq.toList).filter (fun e => e ∈ t.fs.map ⟨ fun a => a.1 , by simp [Function.Injective]⟩)).map ToString.toString
    have δ : List String := (fq.toList).map (fun a => String.join ((fσ.toList).map (fun b => if h : a ∈ t.qs ∧ b ∈ σs then "("++ ToString.toString a ++ "×" ++ ToString.toString b ++ ")→" ++ ToString.toString (t.δ ⟨a , h.1⟩ ⟨b , h.2⟩) ++ " " else "")))
    exact "Σ: { " ++ String.join (s.map (fun e => e++" ")) ++ "}\n" ++
          "Q: { " ++ String.join (qss.map (fun e => e++" ")) ++ "}\n" ++
          "δ: " ++ String.join (δ.map (fun e => "\n   "++e)) ++ "\n" ++
          "q₀: " ++ q ++ "\n" ++
          "F: { " ++ String.join (fs.map (fun e => e++" ")) ++ "}\n"


-- δ* function
-- the state reached after following all transitions given a word
-- the first letter in list is the last character consumed
@[simp]
def δ_star' (q : t.qs) : (w : word σs) → t.qs
  | [] => q
  | e :: es => δ_star' (t.δ q e) es


def δ_star : (w : word σs) → t.qs := δ_star' t t.q₀

-- whether a DFA accepts a word
@[simp]
def dfa_accepts : (w : word σs) → Prop := fun w => δ_star t w ∈ t.fs

def dfaLang : Lang σs := fun w => dfa_accepts t w

-- state is reachable from the given state
inductive reachable (q : t.qs) : t.qs → Prop where
  | base : reachable q q
  | step (q' : t.qs) : reachable q q' → ∀ e : σs , reachable q (t.δ q' e)

theorem reachable_trans' (a b : t.qs) : reachable t a b → (c : t.qs) → reachable t b c → reachable t a c := by
  intro h
  induction h with
  | base => intro c ac; exact ac
  | step q _ e s =>  intro c qec
                     apply s
                     induction qec with
                     | base => apply reachable.step; exact reachable.base
                     | step q' _ e' s' => apply reachable.step; exact s'

theorem reachable.trans (a b c : t.qs) : reachable t a b → reachable t b c → reachable t a c := by
  intro a
  apply reachable_trans'
  exact a

-- DFA language is decidable
instance decidableLang (w : word σs) : Decidable (dfa_accepts t w) := by
  simp only [dfa_accepts]
  apply Finset.decidableMem _ _


-- dfa accepts nil iff s is final
theorem dfa_accepts_nil_iff_final : dfa_accepts t [] ↔ t.q₀ ∈ t.fs := by
  apply Iff.intro
  <;> intro h
  <;> (first | simp [dfa_accepts])
  <;> exact h

lemma δ_δ_star'_concat_eq_δ_star' : (q : t.qs) → DFA.δ t (δ_star' t q l) a = δ_star' t q (l ++ [a]) := by
  induction l with
  | nil => simp
  | cons e es s => intro q
                   simp only [δ_star',List.append_eq]
                   apply s (DFA.δ t q e)

theorem δ_star_append_eq (r : word σs) : (l : word σs) → δ_star t (l++r) = δ_star' t (δ_star t l) r := by
  induction r with
  | nil => simp
  | cons a as s => intro l
                   have : l ++ a :: as = l ++ [a] ++ as := by simp
                   rw [this,s]
                   simp [δ_star,δ_δ_star'_concat_eq_δ_star']

theorem δ_star'_append_eq (r : word σs) (a : t.qs) : (l : word σs) → δ_star' t a (l++r) = δ_star' t (δ_star' t a l) r := by
  induction r with
  | nil => simp
  | cons a as s => intro l
                   have : l ++ a :: as = l ++ [a] ++ as := by simp
                   rw [this,s]
                   simp [δ_star,δ_δ_star'_concat_eq_δ_star']

lemma δ_star'_reachable (w : word σs) (q : t.qs) : (q' : t.qs) → reachable t q q' → reachable t q (δ_star' t q' w) := by
  induction w with
  | nil => simp [δ_star]
  | cons e es s => intro q' rq'
                   rw [δ_star']
                   apply s
                   apply reachable.step
                   exact rq'

theorem accepts_from_state_if (w : word σs) (q : t.qs) : (∀ q' : t.qs , (reachable t q q' → q' ∈ t.fs)) → δ_star' t q w ∈ t.fs := by
  intro q'
  apply q'
  apply δ_star'_reachable
  exact reachable.base

theorem state_reachable_iff (q q' : t.qs) : reachable t q q' ↔ ∃ w : word σs , δ_star' t q w = q' := by
  apply Iff.intro
  · intro rq'
    induction rq' with
    | base => exists []
    | step qc _ e s => apply Exists.elim s
                       intro w δ'
                       exists List.concat w e
                       simp [List.concat_eq_append,←δ_δ_star'_concat_eq_δ_star',δ']
  · intro ex
    apply Exists.elim ex
    intro w δ'
    simp only [δ_star'] at δ'
    rw [←δ']
    apply δ_star'_reachable
    exact reachable.base

theorem ex_ne_nil_accepted_iff (h' : t.q₀ ∉ t.fs) : (∃ w, w ∈ dfaLang t ∧ w ≠ []) ↔ ∃ f ∈ t.fs, reachable t t.q₀ f := by
  simp only [dfaLang,dfa_accepts,δ_star]
  apply Iff.intro
  · intro h
    apply Exists.elim h
    intro w win
    rw [Set.mem_def] at win
    exists (δ_star' t t.q₀ w)
    use win.1
    rw [state_reachable_iff]
    exists w
  · intro h
    apply Exists.elim h
    intro q qin
    have : ∃ w : word σs , δ_star' t t.q₀ w = q := (state_reachable_iff t t.q₀ q).mp qin.2
    apply Exists.elim this
    intro w weq
    have : dfa_accepts t w := by simp only [dfa_accepts,δ_star]; rw [weq]; exact qin.1
    cases Decidable.em (w = []) with
    | inl h => rw [h] at this
               simp only [dfa_accepts,δ_star,δ_star'] at this
               contradiction
    | inr h => exists w

lemma reachable_δ_star' (w : word σs) (q : t.qs) : (q' : t.qs) → reachable t (δ_star' t q' w) q → reachable t q' q := by
  match w with
  | [] => simp
  | e::es => intro a r
             apply (state_reachable_iff t a q).mpr
             have := (state_reachable_iff t (δ_star' t a (e :: es)) q).mp r
             apply Exists.elim this
             intro w eq
             rw [←δ_star'_append_eq] at eq
             exists e :: es ++ w

theorem accepts_prefix_if (l r : word σs) : (∀ q' : t.qs , (reachable t (δ_star t l) q' → q' ∈ t.fs)) → dfa_accepts t (l ++ r) := by
  intro fa
  rw [dfa_accepts,δ_star_append_eq]
  apply accepts_from_state_if
  intro q' rq'
  apply fa
  exact rq'

-- To prove that DFA accepts any word starting with a prefix
-- If after l, a state is reached from which all combinations of transitions lead
-- to a final state, it always
theorem accepts_prefix_iff (p : word σs) : (∀ s : word σs , dfa_accepts t (p ++ s)) ↔ dfa_accepts t p ∧ (∀ q' : t.qs , (reachable t (δ_star t p) q' → q' ∈ t.fs)) := by
  apply Iff.intro
  · intro h
    simp only [dfa_accepts] at h
    apply And.intro
    · have : p = p ++ [] := by simp
      rw [this]
      apply h
    · intro q' r
      have := Iff.mp (state_reachable_iff t (δ_star t p) q') r
      apply Exists.elim this
      intro w δ'
      rw [←δ_star_append_eq] at δ'
      rw [←δ']
      exact h w
  · intro h s
    apply accepts_prefix_if
    apply h.2

lemma accepts_suffix_if (l r : word σs) : (∀ q : t.qs , reachable t t.q₀ q → δ_star' t q r ∈ t.fs) → dfa_accepts t (l ++ r) := by
  intro fa
  simp only [dfa_accepts]
  rw [δ_star_append_eq]
  apply fa
  apply δ_star'_reachable
  exact reachable.base

-- To prove that DFA always accepts some suffix
-- If from any reachable state the word is accepted, it is always accepted
theorem accepts_suffix_iff (s : word σs) : (∀ p : word σs,  dfa_accepts t (p ++ s)) ↔ (∀ q : t.qs , reachable t t.q₀ q → δ_star' t q s ∈ t.fs) := by
  apply Iff.intro
  · intro fa q rq
    have := Iff.mp (state_reachable_iff t t.q₀ q) rq
    apply Exists.elim this
    intro w δ'
    rw [←δ']
    have : δ_star' t t.q₀ w = δ_star t w := by simp [δ_star]
    rw [this, ←δ_star_append_eq]
    apply fa
  · intro fa w
    apply accepts_suffix_if
    exact fa

-- Define whether list forms path between start and finish
-- The elements (vertices) are joined by edges and each vertex exists at most once
-- The last element must be the target
def is_path (a z : t.qs) : List t.qs → Prop
  | [] => a = z
  | q :: qs => (∃ e : σs , t.δ a e = q) ∧ is_path q z qs ∧ q ∉ qs


theorem target_in_path  (l : List t.qs) : (a b : t.qs) → is_path t a b l → a ≠ b → b ∈ l := by
  induction l with
  | nil => intro a b pab _; simp [is_path] at pab; contradiction
  | cons e es s => intro a b pab _;
                   simp only [is_path] at pab
                   have := s e b
                   cases (Decidable.em (b=e)) with
                   | inl h => apply List.mem_cons.mpr
                              apply Or.inl
                              exact h
                   | inr h => apply List.mem_cons.mpr
                              apply Or.inr
                              apply this
                              exact pab.2.1
                              intro eq
                              apply h
                              rw [eq]

lemma all_in_path_reachable (l : List t.qs) : (a b : t.qs) → is_path t a b l → ∀ q : t.qs, q ∈ l → reachable t a q := by
  induction l with
  | nil => intro a b _ q qin; contradiction
  | cons e es s => intro a b p q qinees
                   simp only [is_path] at p
                   cases (Decidable.em (q=e)) with
                   | inr h => have qines := List.mem_of_ne_of_mem h qinees
                              have req : reachable t e q := by apply s
                                                               exact p.2.1
                                                               exact qines
                              have rae : reachable t a e := by apply Exists.elim (p.1)
                                                               intro s δs
                                                               apply (Iff.mpr (state_reachable_iff t a e))
                                                               exists [s]
                              apply reachable.trans
                              · exact rae
                              · exact req
                   | inl h => simp [is_path] at p
                              apply (Iff.mpr (state_reachable_iff t a q))
                              rw [←h] at p
                              apply Exists.elim p.1
                              intro s δs
                              apply Exists.elim δs
                              intro sin δ
                              exists [⟨s, sin⟩]


-- Gets all elements from list until it encouters an element (includes the element in result)
def list_until {α : Type _} (a : α) [DecidableEq α] : List α → List α
  | [] => []
  | e::es => if e=a then [e] else e::list_until a es

def nin_list_nin_list_until {α : Type _} [DecidableEq α] (a : α) (l : List α) : a ∉ l → ∀ b : α, a ∉ list_until b l := by
  induction l with
  | nil => simp [list_until]
  | cons e es s => intro anin b
                   simp only [list_until]
                   split
                   ·  simp
                      exact List.ne_of_not_mem_cons anin
                   ·  simp
                      intro or
                      apply Or.elim or
                      · intro eq
                        apply List.ne_of_not_mem_cons anin
                        exact eq
                      · intro ain
                        have := List.not_mem_of_not_mem_cons anin
                        apply s
                        · exact this
                        · exact ain


lemma path_if_list_until (l : List t.qs) : (a b : t.qs) → is_path t a b l → ∀ q : t.qs, q ∈ l → is_path t a q (list_until q l) := by
  induction l with
  | nil => intro a b _ q qin; contradiction
  | cons e es s => intro a b pab q qin
                   simp only [is_path] at pab
                   simp only [list_until]
                   split
                   · simp only [is_path]
                     apply And.intro
                     · exact pab.1
                     · exact ⟨by assumption,by simp⟩
                   · simp only [is_path]
                     apply And.intro
                     · exact pab.1
                     apply And.intro
                     · apply s
                       · exact pab.2.1
                       · apply Or.elim (List.eq_or_mem_of_mem_cons qin)
                         · have h : ¬e=q := by assumption
                           intro qe
                           rw [←qe] at h
                           contradiction
                         · intro qin
                           exact qin
                     · apply nin_list_nin_list_until
                       exact pab.2.2



lemma all_in_path_path (l : List t.qs) : (a b : t.qs) → is_path t a b l → ∀ q : t.qs, q ∈ l → ∃ l₁ : List t.qs, is_path t a q l₁ := by
  match l with
  | [] => intro a b _ q qin; contradiction
  | e::es => intro a b p q qin
             exists list_until q (e::es)
             apply path_if_list_until
             · exact p
             · exact qin


lemma path_concat (l : List t.qs) : (a b c : t.qs) → is_path t a b l → (∃ e : σs, t.δ b e = c) → c ∉ l → is_path t a c (l.concat c) := by
  induction l with
  | nil => intro a b c p ex cin
           simp only [is_path]
           simp only [is_path] at p
           rw [←p] at ex
           apply Exists.elim ex
           intro e _
           apply And.intro
           · exists e
           · simp
  | cons e es s => intro a b c p ex cin
                   simp only [is_path]
                   simp only [is_path] at p
                   apply And.intro
                   · exact p.1
                   · apply And.intro
                     · apply s
                       exact p.2.1
                       exact ex
                       exact List.not_mem_of_not_mem_cons cin
                     · have : c≠e := List.ne_of_not_mem_cons cin
                       rw [List.concat_eq_append]
                       apply List.not_mem_append
                       · exact p.2.2
                       · intro ein
                         have := List.eq_of_mem_singleton ein
                         have := Eq.symm this
                         contradiction


theorem reachable_iff_ex_path (a b : t.qs) : reachable t a b ↔ ∃ l : List t.qs , is_path t a b l := by
  apply Iff.intro
  . intro r
    induction r with
    | base => exists []
    | step c _ e s =>  generalize δq : DFA.δ t c e = q
                       apply Exists.elim s
                       intro l p
                       cases (Decidable.em (q ∈ l)) with
                       | inr h => exists l.concat q
                                  apply path_concat
                                  · exact p
                                  · exists e
                                  · exact h
                       | inl h => apply all_in_path_path
                                  · exact p
                                  · exact h
  · intro ex
    apply Exists.elim ex
    intro l pab
    cases (Decidable.em (a=b)) with
    | inl h => rw [h]; exact reachable.base
    | inr h => apply all_in_path_reachable
               · exact pab
               · simp only [is_path] at pab
                 apply target_in_path
                 exact pab
                 exact h



theorem path_nodup (l : List t.qs) : (a b : t.qs) → is_path t a b l → l.Nodup := by
  induction l with
  | nil => simp
  | cons e es s => intro a b h
                   simp only [is_path] at h
                   simp only [List.nodup_cons]
                   apply And.intro
                   · apply h.2.2
                   · apply s
                     · exact h.2.1

lemma path_finset_subset (l : List t.qs) : (a b : t.qs) → is_path t a b l → l.toFinset ⊆ t.qs.attach := by
  intro a b _
  simp only [· ⊆ · ]
  intro e _
  apply Finset.mem_attach

theorem path_le_size (l : List t.qs) : (a b : t.qs) → is_path t a b l → l.length ≤ t.qs.card := by
  intro a b pab
  rw [←Finset.card_attach,←List.toFinset_card_of_nodup]
  apply Finset.card_le_of_subset
  apply path_finset_subset
  exact pab
  apply path_nodup
  exact pab


theorem w_le_card_if_ex_w  (p : word t.qs) : (a b : t.qs) → is_path t a b p → (∃ w : word σs, δ_star' t a w = b ∧ w.length = p.length) := by
  induction p with
  | nil => intro a b p
           exists []
  | cons e es s => intro a b p
                   simp only [is_path] at p
                   have := s e b p.2.1
                   apply Exists.elim this
                   intro w h
                   apply Exists.elim p.1
                   intro s eq
                   exists s::w
                   simp only [δ_star',List.length]
                   rw [h.2]
                   apply And.intro
                   · rw [eq]
                     exact h.1
                   · rfl


theorem ex_w_iff_ex_w_le_card (a b : t.qs) : (∃ w : word σs, δ_star' t a w = b) ↔ (∃ w : word σs, δ_star' t a w = b ∧ w.length <= t.qs.card) := by
  apply Iff.intro
  · intro ex
    have := (state_reachable_iff t a b).mpr ex
    have := (reachable_iff_ex_path t a b).mp this
    apply Exists.elim this
    intro p isp
    have := w_le_card_if_ex_w t p a b isp
    apply Exists.elim this
    intro w h
    exists w
    apply And.intro
    · exact h.1
    · have := path_le_size t p a b isp
      rw [←h.2] at this
      exact this
  · intro ex
    apply Exists.elim ex
    intro w h
    exists w
    exact h.1

instance DecidableExW {P : word σs → Prop} [f : Fintype {x : word σs // x.length <= t.qs.card}] [DecidablePred P] : Decidable (∃ w : {x : word σs // x.length <= t.qs.card}, P w ) := by
  have h : Decidable (∃ l, l ∈ f.elems ∧ (fun l => P l) l) := Finset.decidableExistsAndFinset
  match h with
  | isTrue t => apply isTrue
                apply Exists.elim t
                intro w h
                exists w
                exact h.2
  | isFalse g => apply isFalse
                 intro ex
                 apply g
                 apply Exists.elim ex
                 intro w h
                 exists w
                 apply And.intro
                 · apply f.complete
                 · exact h

instance decIsPath : (a b : t.qs) → Decidable (is_path t a b w) := by
  induction w with
  | nil => simp only [is_path]
           infer_instance
  | cons e es => simp only [is_path]
                 intro a b
                 infer_instance

instance decExIsPath : (a b : t.qs) → Decidable (∃ l : List t.qs, is_path t a b l) := by
  intro a b
  have f : Fintype {p : List t.qs // p.Nodup} := fintypeNodupList
  have h : Decidable (∃ l, l ∈ f.elems ∧ (fun l => is_path t a b l) l) := Finset.decidableExistsAndFinset
  match h with
  | isTrue t => apply isTrue
                apply Exists.elim t
                intro l la
                exists l
                exact la.right
  | isFalse g => apply isFalse
                 intro ex
                 apply g
                 apply Exists.elim ex
                 intro l la
                 exists ⟨l , path_nodup t l a b la⟩
                 apply And.intro
                 · apply f.complete
                 · simp only [List.Nodup]
                   exact la

instance decReachable : DecidableRel (reachable t) := by
  intro a b
  apply decidable_of_iff (∃ l : List t.qs, is_path t a b l)
  apply Iff.symm
  apply reachable_iff_ex_path

instance decExδStar' : Decidable (∃ w : word σs, δ_star' t a w = b) := by
  apply decidable_of_iff (reachable t a b)
  exact (state_reachable_iff t a b)

-- Structure
-- Exists reachable final state that is not starting state?
--  yes : exists
--  no : is start state in final states?
--    no : doesn't exist
--    yes : is there a path from start state to start state?
--      no : doesn't exist
--      yes : exists
instance decAcceptsNeNil : Decidable (∃ w, dfa_accepts t w ∧ w ≠ []) := by
  simp only [dfa_accepts]
  have : Decidable (∃ f ∈ t.fs, f ≠ t.q₀ ∧ reachable t t.q₀ f) := by infer_instance
  match this with
  | isTrue h => apply Decidable.isTrue
                apply Exists.elim h
                intro q h
                have := (state_reachable_iff t t.q₀ q).mp h.2.2
                apply Exists.elim this
                intro w eq
                exists w
                simp only [δ_star]
                rw [eq]
                use h.1
                intro nil
                rw [nil] at eq
                simp only [δ_star'] at eq
                rw [←eq] at h
                apply h.2.1
                rfl
  | isFalse h => have g : Decidable (t.q₀ ∈ t.fs) := by infer_instance
                 match g with
                 | isTrue h'=> have d : Decidable (∃ e : σs,(fun e => ∃ w, δ_star' t (t.δ t.q₀ e) w = t.q₀) e ) := Fintype.decidableExistsFintype
                               match d with
                               | isTrue ex => apply Decidable.isTrue
                                              apply Exists.elim ex
                                              intro e eex
                                              apply Exists.elim eex
                                              intro w weq
                                              exists (e::w)
                                              simp only [δ_star,δ_star']
                                              rw [weq]
                                              use h'
                                              simp
                                | isFalse ex => apply Decidable.isFalse
                                                intro ex'
                                                apply h
                                                apply Exists.elim ex'
                                                intro w wne
                                                exists δ_star t w
                                                use wne.1
                                                apply And.intro
                                                · intro eq
                                                  rw [eq] at wne
                                                  apply ex
                                                  match w with
                                                  | [] => have : [] ≠ [] := wne.2
                                                          contradiction
                                                  | e::es => exists e
                                                             exists es
                                                · simp only [δ_star]
                                                  apply δ_star'_reachable
                                                  exact reachable.base
                 | isFalse h' => apply Decidable.isFalse
                                 intro ex
                                 apply h
                                 apply Exists.elim ex
                                 intro w h
                                 exists δ_star t w
                                 use h.1
                                 cases Decidable.em (t.q₀ = δ_star t w) with
                                 | inl eq => rw [←eq] at h
                                             have : t.q₀ ∈ t.fs := h.1
                                             contradiction
                                 | inr eq => rw [←eq_comm] at eq
                                             use eq
                                             rw [state_reachable_iff]
                                             exists w


instance decExPrefix : Decidable (∃ a b, dfa_accepts t a ∧ a ++ b = w) := by
  have f : Fintype {p : List σs // p.length <= w.length} := by infer_instance
  have h : Decidable (∃ l, l ∈ f.elems ∧ (fun l => ∃ b, b ∈ f.elems ∧ l.1++b.1 = w ∧ dfa_accepts t l.1) l) := Finset.decidableExistsAndFinset
  match h with
  | isTrue t => apply isTrue
                apply Exists.elim t
                intro l la
                exists l
                simp at la
                apply Exists.elim la.2
                intro lb h
                exists lb
                simp only [dfa_accepts]
                use h.2.2
                exact h.2.1
  | isFalse g => apply isFalse
                 intro ex
                 apply g
                 apply Exists.elim ex
                 intro a ex
                 apply Exists.elim ex
                 intro b h
                 have t₁ := List.length_append a b
                 have t₂ : List.length a + List.length b = List.length w := by rw [←t₁,←h.2]
                 have h₁ : List.length a <= List.length w := by rw [←t₂]; simp
                 have h₂ : List.length b <= List.length w := by rw [←t₂]; simp
                 exists ⟨a,h₁⟩
                 apply And.intro
                 · apply Fintype.complete
                 · simp
                   exists b
                   apply And.intro
                   · exists h₂
                     apply Fintype.complete
                   · rw [And.comm]
                     exact h


end DFA

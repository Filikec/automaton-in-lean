import Automaton.Language.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.FinEnum
import Automaton.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.List
import Mathlib.Data.Vector.Basic
import Mathlib.Data.List.Card

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


structure DFA (σ : Type _) where
  q : Type _             -- states
  init : q               -- initial state
  fs : Finset q          -- accepting states
  δ : q → σ → q          -- transition function
  [fq : FinEnum q]
  [fσ : FinEnum σ]

variable {σ : Type _} [FinEnum σ] (r s t : DFA σ)

instance : FinEnum t.q := t.fq

-- δ* function
-- the state reached after following all transitions given a word
-- the first letter in list is the last character consumed
@[simp]
def δ_star' (q : t.q) : (w : word σ) → t.q
  | [] => q
  | e :: es => δ_star' (t.δ q e) es 


def δ_star : (w : word σ) → t.q := δ_star' t t.init

-- whether a DFA accepts a word
@[simp]
def dfa_accepts : (w : word σ) → Prop := by
  intro w
  exact δ_star t w ∈ t.fs

def dfaLang : Lang σ := fun w => dfa_accepts t w


-- all states reachable from current state
inductive reachable (q : t.q) : t.q → Prop where
  | base : reachable q q
  | step (q' : t.q) : reachable q q' → ∀ e : σ , reachable q (t.δ q' e)


theorem reachable_trans' (a b : t.q) : reachable t a b → (c : t.q) → reachable t b c → reachable t a c := by
  intro h
  induction h with
  | base => intro c ac; exact ac
  | step q _ e s =>  intro c qec
                     apply s
                     induction qec with
                     | base => apply reachable.step; exact reachable.base
                     | step q' _ e' s' => apply reachable.step; exact s' 

theorem reachable.trans (a b c : t.q) : reachable t a b → reachable t b c → reachable t a c := by
  intro a
  apply reachable_trans'
  exact a

-- DFA language is decidable
instance decidableLang (w : word σ) : Decidable (dfa_accepts t w) := by
  simp only [dfa_accepts]
  have : DecidableEq t.q := by exact t.fq.decEq  
  apply Finset.decidableMem
  
-- equality of DFAs
def eq : Prop := ∀ w : word σ , dfa_accepts t w ↔ dfa_accepts s w

private theorem eq.refl : eq t t := by
  intro w
  apply Iff.intro <;> (intro ; assumption) 

private theorem eq.trans : eq t s → eq s r → eq t r := by
  intro eq₁ eq₂
  intro w
  apply Iff.intro
  · intro r
    apply (Iff.mp (eq₁ w))
    apply (Iff.mp (eq₂ w))
    exact r
  · intro t
    apply (Iff.mpr (eq₂ w))
    apply (Iff.mpr (eq₁ w))
    exact t

private theorem eq.sym : eq t s → eq s t := by
  intro h
  intro w
  apply Iff.intro 
  <;> intro 
  <;> (first | apply (Iff.mp (h w)) | apply (Iff.mpr (h w))) 
  <;> assumption


-- dfa accepts nil iff init is final
theorem dfa_accepts_nil_iff_final : dfa_accepts t [] ↔ t.init ∈ t.fs := by
  apply Iff.intro 
  <;> intro h 
  <;> (first | simp [dfa_accepts])
  <;> exact h

lemma δ_δ_star'_concat_eq_δ_star' : (q : t.q) → DFA.δ t (δ_star' t q l) a = δ_star' t q (l ++ [a]) := by
  induction l with
  | nil => simp
  | cons e es s => intro q
                   simp only [δ_star',List.append_eq]
                   apply s (DFA.δ t q e)

theorem δ_star_append_eq (r : word σ) : (l : word σ) → δ_star t (l++r) = δ_star' t (δ_star t l) r := by
  induction r with
  | nil => simp
  | cons a as s => intro l
                   have : l ++ a :: as = l ++ [a] ++ as := by simp
                   rw [this,s]
                   simp [δ_star,δ_δ_star'_concat_eq_δ_star']



lemma δ_star'_reachable (w : word σ) (q : t.q) : (q' : t.q) → reachable t q q' → reachable t q (δ_star' t q' w) := by
  induction w with
  | nil => simp [δ_star]
  | cons e es s => intro q' rq' 
                   rw [δ_star']
                   apply s
                   apply reachable.step
                   exact rq'
  

theorem accepts_from_state_if (w : word σ) (q : t.q) : (∀ q' : t.q , (reachable t q q' → q' ∈ t.fs)) → δ_star' t q w ∈ t.fs := by
  intro q'
  apply q'
  apply δ_star'_reachable
  exact reachable.base 

theorem state_reachable_iff (q q' : t.q) : reachable t q q' ↔ ∃ w : word σ , δ_star' t q w = q' := by
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

theorem accepts_prefix_if (l r : word σ) : (∀ q' : t.q , (reachable t (δ_star t l) q' → q' ∈ t.fs)) → dfa_accepts t (l ++ r) := by
  intro fa
  rw [dfa_accepts,δ_star_append_eq]
  apply accepts_from_state_if
  intro q' rq'
  apply fa
  exact rq'

-- To prove that DFA accepts any word starting with a prefix
-- If after l, a state is reached from which all combinations of transitions lead
-- to a final state, it always
theorem accepts_prefix_iff (p : word σ) : dfa_accepts t p ∧ (∀ q' : t.q , (reachable t (δ_star t p) q' → q' ∈ t.fs)) ↔ ∀ s : word σ , dfa_accepts t (p ++ s) := by
  apply Iff.intro
  · intro h s
    apply accepts_prefix_if
    apply h.2
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

lemma accepts_suffix_if (l r : word σ) : (∀ q : t.q , reachable t t.init q → δ_star' t q r ∈ t.fs) → dfa_accepts t (l ++ r) := by
  intro fa
  simp only [dfa_accepts]
  rw [δ_star_append_eq]
  apply fa
  apply δ_star'_reachable
  exact reachable.base 
  
-- To prove that DFA always accepts some suffix
-- If from any reachable state the word is accepted, it is always accepted
theorem accepts_suffix_iff (s : word σ) : (∀ p : word σ,  dfa_accepts t (p ++ s)) ↔ (∀ q : t.q , reachable t t.init q → δ_star' t q s ∈ t.fs) := by
  apply Iff.intro
  · intro fa q rq
    have := Iff.mp (state_reachable_iff t t.init q) rq
    apply Exists.elim this
    intro w δ'
    rw [←δ']
    have : δ_star' t t.init w = δ_star t w := by simp [δ_star]
    rw [this, ←δ_star_append_eq]
    apply fa
  · intro fa w
    apply accepts_suffix_if
    exact fa

-- Define whether list forms path between start and finish
-- The elements (vertices) are joined by edges and each vertex exists at most once
-- The last element must be the target
def is_path (a z : t.q) (l : List t.q) : Bool := by
  match l with
  | [] => exact decide (a = z)
  | q :: qs => exact decide (∃ e : σ , t.δ a e = q) && is_path q z qs && decide (q ∉ qs)


theorem target_in_path  (l : List t.q) : (a b : t.q) → is_path t a b l → a ≠ b →  b ∈ l := by
  induction l with
  | nil => intro a b pab _; simp [is_path] at pab; contradiction
  | cons e es s => intro a b pab _;
                   simp [is_path] at pab
                   have := s e b pab.1.2
                   cases (Decidable.em (b=e)) with
                   | inl h => apply List.mem_cons.mpr
                              apply Or.inl
                              exact h
                   | inr h => apply List.mem_cons.mpr
                              apply Or.inr
                              apply this
                              simp only [·≠· ]
                              intro d
                              rw [d] at h
                              contradiction

lemma all_in_path_reachable (l : List t.q) : (a b : t.q) → is_path t a b l → ∀ q : t.q, q ∈ l → reachable t a q := by
  induction l with
  | nil => intro a b _ q qin; contradiction
  | cons e es s => intro a b p q qinees
                   cases (Decidable.em (q=e)) with
                   | inr h => have qines := List.mem_of_ne_of_mem h qinees
                              simp [is_path] at p
                              have req : reachable t e q := by apply s
                                                               exact p.1.2
                                                               exact qines
                              have rae : reachable t a e := by apply Exists.elim (p.1.1)
                                                               intro s δs 
                                                               apply (Iff.mpr (state_reachable_iff t a e))
                                                               exists [s]
                              apply reachable.trans
                              · exact rae
                              · exact req 
                   | inl h => simp [is_path] at p
                              apply (Iff.mpr (state_reachable_iff t a q))
                              rw [←h] at p
                              apply Exists.elim p.1.1
                              intro s δs
                              exists [s]
                   

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

lemma path_if_list_until (l : List t.q) : (a b : t.q) → is_path t a b l → ∀ q : t.q, q ∈ l → is_path t a q (list_until q l) := by
  induction l with
  | nil => intro a b _ q qin; contradiction
  | cons e es s => intro a b pab q qin 
                   simp [is_path] at pab
                   simp only [list_until]
                   split 
                   · simp [is_path]
                     apply And.intro
                     · exact pab.1.1
                     · assumption
                   · simp [is_path]  
                     apply And.intro
                     · apply And.intro
                       · exact pab.1.1
                       · apply s
                         · exact pab.1.2
                         · apply Or.elim (List.eq_or_mem_of_mem_cons qin)
                           · have h : ¬e=q := by assumption
                             intro qe
                             rw [←qe] at h
                             contradiction
                           · intro qin
                             exact qin
                     · apply nin_list_nin_list_until
                       exact pab.2
                   

lemma all_in_path_path (l : List t.q) : (a b : t.q) → is_path t a b l → ∀ q : t.q, q ∈ l → ∃ l₁ : List t.q, is_path t a q l₁ := by
  match l with
  | [] => intro a b _ q qin; contradiction
  | e::es => intro a b p q qin
             exists list_until q (e::es)
             apply path_if_list_until
             · exact p
             · exact qin


lemma path_concat (l : List t.q) : (a b c : t.q) → is_path t a b l → (∃ e : σ , t.δ b e = c) → c ∉ l → is_path t a c (l.concat c) := by
  induction l with
  | nil => intro a b c p ex cin
           simp [is_path]
           simp[is_path] at p
           rw [←p] at ex; exact ex
  | cons e es s => intro a b c p ex cin
                   simp [is_path]
                   simp [is_path] at p
                   apply And.intro
                   · apply And.intro
                     · exact p.1.1
                     · rw [←List.concat_eq_append]
                       apply s
                       · exact p.1.2
                       · exact ex
                       · exact List.not_mem_of_not_mem_cons cin
                   · apply And.intro
                     · exact p.2
                     · have : c≠e := List.ne_of_not_mem_cons cin
                       intro ec
                       apply this
                       rw [ec]

theorem reachable_iff_ex_path (a b : t.q) : reachable t a b ↔ ∃ l : List t.q , is_path t a b l := by
  apply Iff.intro
  . intro r
    induction r with
    | base => exists []
              simp [is_path]
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
               · simp [is_path] at pab
                 apply target_in_path
                 exact pab 
                 exact h

    
theorem path_Nodup (l : List t.q) : (a b : t.q) → is_path t a b l → l.Nodup := by
  induction l with
  | nil => simp
  | cons e es s => intro a b h
                   simp only [is_path] at h
                   simp
                   simp at h
                   apply And.intro
                   · apply h.2
                   · apply s
                     · exact h.1.2


theorem path_le_card (l : List t.q) : (a b : t.q) → is_path t a b l → l.card ≤ List.card t.fq.toList := by
  intro a b _
  apply List.card_subset_le
  simp [·⊆·, List.Subset]
  

theorem card_nodup_eq_len [DecidableEq α ] {l : List α} {nd : l.Nodup} : l.card = l.length := by
  induction l with
  | nil => simp
  | cons a as s => simp only [List.card, List.length]
                   split
                   · have ain : a ∈ as := by assumption
                     have : False := (List.nodup_cons.mp nd).left ain
                     contradiction
                   · simp only [·+·,Add.add, Nat.add]
                     apply congr_arg
                     apply s
                     exact (List.nodup_cons.mp nd).right

theorem path_le_size (l : List t.q) : (a b : t.q) → is_path t a b l → l.length ≤ List.length t.fq.toList := by
  intro a b pab
  have h₁ : l.Nodup := path_Nodup t l a b pab 
  have h₂ : List.Nodup t.fq.toList := FinEnum.nodup_toList
  rw [←card_nodup_eq_len]
  rw [←card_nodup_eq_len]
  apply path_le_card
  · exact pab
  · assumption
  · assumption


instance DecidableIsPath : (a b : t.q) → Decidable (∃ l : List t.q, is_path t a b l) := by
  intro a b
  have fin : Fintype t.q := ⟨ List.toFinset t.fq.toList, by simp⟩ 
  have f : Fintype {l : List t.q // l.Nodup} := @fintypeNodupList t.q t.fq.decEq fin
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
                 exists ⟨l , path_Nodup t l a b la⟩
                 apply And.intro
                 · apply f.complete
                 · simp only [List.Nodup]
                   exact la


instance DecidableReachable : DecidableRel (reachable t) := by
  intro a b
  apply decidable_of_iff (∃ l : List t.q, is_path t a b l)
  apply Iff.symm
  apply reachable_iff_ex_path





end DFA
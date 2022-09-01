import data.fin.basic
import data.fintype.basic
import data.list
import computability.regular_expressions
import .automata_typeclass

section re

variables {Sigma : Type} [decidable_eq Sigma]

inductive RE (Sigma : Type*)
| empty : RE
| lit : Sigma → RE
| union : RE → RE → RE
| epsilon : RE
| star : RE → RE
| append : RE → RE → RE

open RE

def union_lang (P Q : lang Sigma) : lang Sigma 
:= λ w , P w ∨ Q w 

inductive star_lang (P : lang Sigma) : lang Sigma 
| empty_star : star_lang []
| extend : ∀ u w, P u → star_lang w 
    → star_lang (u ++ w) 

def append_lang (P Q : lang Sigma) : lang Sigma 
:= λ w, ∃ u v : word Sigma, P u ∧ Q v ∧ w = u ++ v    

def re_lang : RE Sigma → lang Sigma
| empty := λ w , false
| (lit x) := λ w, w = x :: []
| (union r s) := union_lang (re_lang r) (re_lang s)
| epsilon := λ w, w = []
| (star r) := star_lang (re_lang r) 
| (append r s) := append_lang (re_lang r) (re_lang s)

def re2ε_nfa : RE Sigma → ε_nfa Sigma
| empty := empty_ε_nfa
| (lit x) := single_ε_nfa x
| (union r s) := let 
  ra := re2ε_nfa r, 
  sa := re2ε_nfa s
  in {
    Q := ra.Q ⊕ sa.Q,
    finQ := @sum.fintype ra.Q sa.Q ra.finQ sa.finQ,
    decQ := @sum.decidable_eq ra.Q ra.decQ sa.Q sa.decQ,
    inits := λ q, sum.cases_on q ra.inits sa.inits,
    decI := begin 
      assume a,
      letI dr := ra.decI, letI ds := sa.decI,
      cases a;
      tauto,
    end,
    final := λ q, sum.cases_on q ra.final sa.final,
    decF := begin
      assume a,
      letI dr := ra.decF, letI ds := sa.decF,
      cases a;
      tauto,
    end,
    δ := λ a, sum.cases_on a
      (λ a x b, sum.cases_on b (λ b, ra.δ a x b) (λ _, false))
      (λ a x b, sum.cases_on b (λ _, false) (λ b, sa.δ a x b)),
    decD := begin
      assume a,
      simp at *,
      dsimp [sigma.uncurry],
      cases a with ax b,
      cases ax with a x,
      cases a, 
      {
        cases b,
        simp at *,
        exact ra.decD ⟨⟨a, x⟩, b⟩,
        simp at *,
        exact is_false id,
      },
      {
        cases b,
        simp at *,
        exact is_false id,
        simp at *,
        exact sa.decD ⟨⟨a, x⟩, b⟩,
      }
    end,
  }
| epsilon := epsilon_ε_nfa
| (star r) := let
  ra := re2ε_nfa r
  in {
    Q := ra.Q,
    finQ := ra.finQ,
    decQ := ra.decQ,
    inits := ra.inits,
    decI := ra.decI,
    final := λ q, ra.final q ∨ ra.inits q,
    decF := begin 
      letI dI := ra.decI,
      letI dF := ra.decF,
      apply_instance,
    end,
    δ := λ a x b, ra.δ a x b ∨ (ra.final a ∧ ra.inits b ∧ x = none),
    decD := begin
      assume x,
      dsimp [sigma.uncurry],
      cases ra.decD ⟨⟨x.fst.fst, x.fst.snd⟩, x.snd⟩ with n y,
      cases ra.decF x.fst.fst with nn yy,
      letI not : ¬(ra.δ x.fst.fst x.fst.snd x.snd ∨ ra.final x.fst.fst ∧ ra.inits x.snd ∧ x.fst.snd = none),
        assume h,
        cases h with l r,
        dsimp [sigma.uncurry] at n,
        exact n l,
        apply nn,
        exact and.elim_left r,
      exact is_false not,
      cases ra.decI x.snd with nnn yyy,
      letI not : ¬(ra.δ x.fst.fst x.fst.snd x.snd ∨ ra.final x.fst.fst ∧ ra.inits x.snd ∧ x.fst.snd = none),
        assume h,
        cases h with l r,
        dsimp [sigma.uncurry] at n,
        exact n l,
        apply nnn,
        exact and.elim_left (and.elim_right r),
      exact is_false not,
      letI test: decidable_pred (λ x : option Sigma, x = none),
        apply_instance,
      cases test x.fst.snd,
      letI not : ¬(ra.δ x.fst.fst x.fst.snd x.snd ∨ ra.final x.fst.fst ∧ ra.inits x.snd ∧ x.fst.snd = none),
        assume h,
        cases h with l r,
        dsimp [sigma.uncurry] at n,
        exact n l,
        apply h,
        exact and.elim_right (and.elim_right r),
      exact is_false not,
      letI yes : ra.δ x.fst.fst x.fst.snd x.snd ∨ ra.final x.fst.fst ∧ ra.inits x.snd ∧ x.fst.snd = none,
        right,
        exact ⟨yy, ⟨yyy, h⟩⟩,
      exact is_true yes,
      letI yes : ra.δ x.fst.fst x.fst.snd x.snd ∨ ra.final x.fst.fst ∧ ra.inits x.snd ∧ x.fst.snd = none,
        left,
        dsimp [sigma.uncurry] at y,
        exact y,
      exact is_true yes,
    end
  }
| (append r s) := let
  ra := re2ε_nfa r,
  sa := re2ε_nfa s
  in {
    Q := ra.Q ⊕ sa.Q,
    finQ := @sum.fintype ra.Q sa.Q ra.finQ sa.finQ,
    decQ := @sum.decidable_eq ra.Q ra.decQ sa.Q sa.decQ,
    inits := λ q, sum.cases_on q ra.inits (λ _, false),
    decI := begin
      assume a,
      cases a;
      simp at *,
      exact ra.decI a,
      exact is_false id,
    end,
    final := λ q, sum.cases_on q (λ _, false) sa.final,
    decF := begin
      assume a,
      cases a;
      simp at *,
      exact is_false id,
      exact sa.decF a,
    end,
    δ := λ a, sum.cases_on a 
      (λ a x b, sum.cases_on b (λ b, ra.δ a x b) (λ b, ra.final a ∧ sa.inits b ∧ x = none))
      (λ a x b, sum.cases_on b (λ _, false) (λ b, sa.δ a x b)),
    decD := begin
      assume a,
      cases a with ax b, cases ax with a x,
      cases a; cases b; dsimp [sigma.uncurry],
      exact ra.decD ⟨⟨a, x⟩, b⟩,
      {
        letI dF := ra.decF,
        letI dI := sa.decI,
        letI deq := @sum.decidable_eq ra.Q ra.decQ sa.Q sa.decQ,
        apply_instance,
      },
      exact is_false id,
      exact sa.decD ⟨⟨a, x⟩, b⟩,
    end,
  }

theorem re2nfa_lang : ∀ r : RE Sigma, 
  re_lang r = ε_nfa_lang (re2ε_nfa r)
:= sorry

-- not as important

def dfa2re : dfa Sigma → RE Sigma 
:= sorry

def dfa2re_lang : ∀ A : dfa Sigma, 
  dfa_lang A = re_lang (dfa2re A) 
:= sorry

end re 

section pumping
open list
open nat

variable {Sigma : Type}

def rep : ℕ → word Sigma → word Sigma 
| 0 w := []
| (succ n) w := w ++ (rep n w)

theorem pumping_lem : ∀ A : dfa Sigma, ∃ n : ℕ ,
  ∀ s : word Sigma, dfa_lang A s → length s > n → 
  ∀ u v w : word Sigma, s = u ++ v ++ w ∧ length v > 0
  → ∀ i : ℕ, dfa_lang A (u ++ (rep i v) ++ w) := sorry

-- example : show that a^nb^n is not regular

@[derive decidable_eq]
inductive Sigma_ab : Type 
| a : Sigma_ab 
| b : Sigma_ab 

open Sigma_ab 

def anbn : lang Sigma_ab :=
  λ w, ∃ n : ℕ, w = rep n (a :: []) ++ rep n (b :: [])

def Regular : lang Sigma → Prop :=
λ P , exists A : dfa Sigma, P = dfa_lang A

def Regular_nfa : lang Sigma → Prop :=
λ P , exists A : nfa Sigma, P = nfa_lang A

def Regular_re : lang Sigma → Prop :=
λ P , exists A : RE Sigma, P = re_lang A

theorem regular_thm : ∀ P : lang Sigma, 
  (Regular P →  Regular_nfa P) ∧ 
  (Regular_nfa P → Regular_re P) ∧
  (Regular_re P → Regular P) := sorry

theorem nreg_anbn : ¬ (Regular anbn) := sorry 

def asbs : lang Sigma_ab :=
  λ w, ∃ m n : ℕ, w = rep m (a :: []) ++ rep n (b :: [])

theorem reg_asbs : Regular asbs := sorry

def asbs_2 : lang Sigma_ab :=
  λ w, ∃ m n : ℕ, w = rep m (a :: []) ++ rep n (b :: []) 
        ∧ m % 2 == n % 2

theorem reg_asbs_2 : Regular asbs_2 := sorry



end pumping


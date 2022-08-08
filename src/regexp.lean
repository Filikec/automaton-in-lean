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

def re2nfa : RE Sigma → nfa Sigma
| empty := empty_nfa
| (lit x) := single_nfa x
| (union r s) := let 
  ra := re2nfa r, 
  sa := re2nfa s
  in {
    Q := fin ((@fintype.card ra.Q ra.finQ) + (@fintype.card sa.Q sa.finQ)),
    finQ := by apply_instance,
    decQ := by apply_instance,
    inits := λ q, sorry,
    decI := by sorry,
    final := λ q, sorry,
    decF := by sorry,
    δ := λ a x b, sorry,
    decD := sorry,
  }
| epsilon := epsilon_nfa
| (star r) := sorry
| (append r s) := sorry

theorem re2nfa_lang : ∀ r : RE Sigma, 
  re_lang r = nfa_lang (re2nfa r)
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


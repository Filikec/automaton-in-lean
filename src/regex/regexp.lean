import data.fin.basic
import data.fintype.basic
import data.list
import ..automata_typeclass
import ..regex.empty
import ..regex.epsilon
import ..regex.literal
import ..regex.union
import ..regex.append
import ..regex.star

section re

variables {Sigma : Type} [decidable_eq Sigma]

inductive RE (Sigma : Type)
| empty : RE
| lit : Sigma → RE
| union : RE → RE → RE
| epsilon : RE
| star : RE → RE
| append : RE → RE → RE

open RE

def re_lang : RE Sigma → lang Sigma
| empty := empty_lang
| epsilon := epsilon_lang
| (lit x) := lit_lang x 
| (union r s) := union_lang (re_lang r) (re_lang s)
| (star r) := star_lang (re_lang r) 
| (append r s) := append_lang (re_lang r) (re_lang s)

def re2ε_nfa : RE Sigma → ε_nfa Sigma
| empty := empty_ε_nfa
| (lit x) := single_ε_nfa x
| (union r s) := union_ε_nfa (re2ε_nfa r) (re2ε_nfa s)
| epsilon := epsilon_ε_nfa
| (star r) := star_ε_nfa (re2ε_nfa r)
| (append r s) := append_ε_nfa (re2ε_nfa r) (re2ε_nfa s)

theorem re2nfa_lang : ∀ r : RE Sigma, ∀ w : word Sigma,
  re_lang r w ↔ ε_nfa_lang (re2ε_nfa r) w :=
begin
  assume r,
  induction r,
  {
    -- empty
    assume w,
    dsimp [re_lang],
    dsimp [re2ε_nfa],
    exact iff.symm (empty_ε_nfa_lang w),
  },
  {
    -- lit r
    assume w,
    dsimp [re_lang],
    dsimp [re2ε_nfa],
    exact iff.symm (single_ε_nfa_lang r w),
  },
  {
    -- union
    assume w,
    let g := (iff.symm (union_ε_nfa_lang (re2ε_nfa r_ᾰ) (re2ε_nfa r_ᾰ_1) w)),
    let h : union_lang (re_lang r_ᾰ) (re_lang r_ᾰ_1) w 
            ↔ union_lang (ε_nfa_lang (re2ε_nfa r_ᾰ)) (ε_nfa_lang (re2ε_nfa r_ᾰ_1)) w,
      {
        dsimp [union_lang],
        constructor,
        {
          assume h,
          cases h,
          left, exact iff.mp (r_ih_ᾰ w) h,
          right, exact iff.mp (r_ih_ᾰ_1 w) h,
        },
        {
          assume h,
          cases h,
          left, exact iff.mpr (r_ih_ᾰ w) h,
          right, exact iff.mpr (r_ih_ᾰ_1 w) h,
        }
      },
    exact iff.trans h g,
  },
  {
    -- epsilon
    assume w,
    dsimp [re_lang],
    dsimp [re2ε_nfa],
    exact iff.symm (epsilon_ε_nfa_lang w),
  },
  {
    -- star
    assume w,
    let h : star_lang (re_lang r_ᾰ) w ↔ star_lang (ε_nfa_lang (re2ε_nfa r_ᾰ)) w,
      {
        constructor,
        {
          assume h,
          induction h,
          case star_lang.empty_star
          {
            constructor,
          },
          case star_lang.extend : u' w' pu sw ih
          {
            fconstructor,
            exact (r_ih u').mp pu,
            exact ih,
          }
        },
        {
          assume h,
          induction h,
          case star_lang.empty_star
          {
            constructor,
          },
          case star_lang.extend : u' w' pu sw ih
          {
            fconstructor,
            exact (r_ih u').mpr pu,
            exact ih,
          }
        }
      },
    let g := (iff.symm (star_ε_nfa_lang (re2ε_nfa r_ᾰ) w)),
    exact iff.trans h g,
  },
  {
    -- append
    assume w,
    let g := (iff.symm (append_ε_nfa_lang (re2ε_nfa r_ᾰ) (re2ε_nfa r_ᾰ_1) w)),
    let h : append_lang (re_lang r_ᾰ) (re_lang r_ᾰ_1) w 
            ↔ append_lang (ε_nfa_lang (re2ε_nfa r_ᾰ)) (ε_nfa_lang (re2ε_nfa r_ᾰ_1)) w,
    {
      constructor,
      {
        assume h,
        cases h with u h, cases h with v h,
        existsi [u, v],
        cases h with h1 h, cases h with h2 h3,
        constructor,
        exact (r_ih_ᾰ u).mp h1,
        constructor,
        exact (r_ih_ᾰ_1 v).mp h2,
        exact h3,
      },
      {
        assume h,
        cases h with u h, cases h with v h,
        existsi [u, v],
        cases h with h1 h, cases h with h2 h3,
        constructor,
        exact (r_ih_ᾰ u).mpr h1,
        constructor,
        exact (r_ih_ᾰ_1 v).mpr h2,
        exact h3,
      }
    },
    exact iff.trans h g,
  }
end

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

variables {Sigma : Type} [decidable_eq Sigma]

def rep : ℕ → word Sigma → word Sigma 
| 0 w := []
| (succ n) w := w ++ (rep n w)

theorem pumping_lem : ∀ A : dfa Sigma,
  ∀ s : word Sigma, dfa_lang A s → ∃ p : ℕ, length s >= p → 
  ∀ u v w : word Sigma, s = u ++ v ++ w ∧ length v > 0 ∧ length u + length v <= p
  → ∀ i : ℕ, dfa_lang A (u ++ (rep i v) ++ w) :=
begin
  assume A s h_reg,
  sorry,
end

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


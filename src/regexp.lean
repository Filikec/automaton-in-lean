import data.fin.basic
import data.fintype.basic
import data.list
import computability.regular_expressions
import .automata_typeclass

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

def empty_lang : lang Sigma
:= λ _, false

def epsilon_lang : lang Sigma
:= λ w, w = []

def lit_lang (x : Sigma) : lang Sigma
:= λ w, w = x :: []

def union_lang (P Q : lang Sigma) : lang Sigma 
:= λ w , P w ∨ Q w 

inductive star_lang (P : lang Sigma) : lang Sigma 
| empty_star : star_lang []
| extend : ∀ u w, P u → star_lang w 
    → star_lang (u ++ w) 

def append_lang (P Q : lang Sigma) : lang Sigma 
:= λ w, ∃ u v : word Sigma, P u ∧ Q v ∧ w = u ++ v    

def re_lang : RE Sigma → lang Sigma
| empty := empty_lang
| epsilon := epsilon_lang
| (lit x) := lit_lang x 
| (union r s) := union_lang (re_lang r) (re_lang s)
| (star r) := star_lang (re_lang r) 
| (append r s) := append_lang (re_lang r) (re_lang s)

def empty_ε_nfa {Sigma : Type*} [decidable_eq Sigma] : ε_nfa Sigma :=
  {
    Q := fin 1,
    finQ := by apply_instance,
    decQ := by apply_instance,
    inits := λ _ , true,
    decI := by apply_instance,
    final := λ _ , false,
    decF := by apply_instance,
    δ := λ _ _ _ , false,
    decD := λ _, by {dsimp[sigma.uncurry], apply_instance,},
  }

lemma empty_ε_nfa_lang : ∀ w : word Sigma, ε_nfa_lang empty_ε_nfa w ↔ empty_lang w :=
begin 
  assume w,
  dsimp [ε_nfa_lang, empty_lang],
  constructor,
  {
    assume h,
    cases h with q0 h, cases h with q1 h,
    cases and.elim_right (and.elim_right h),
  },
  {
    assume f,
    cases f,
  }
end

def epsilon_ε_nfa {Sigma : Type*} : ε_nfa Sigma :=
  {
    Q := fin 1,
    finQ := by apply_instance,
    decQ := by apply_instance,
    inits := λ _ , true,
    decI := by apply_instance,
    final := λ _ , true,
    decF := by apply_instance,
    δ := λ _ _ _ , false,
    decD := λ _, by {dsimp[sigma.uncurry], apply_instance,},
  }

lemma epsilon_ε_nfa_lang : ∀ w : word Sigma, ε_nfa_lang epsilon_ε_nfa w ↔ epsilon_lang w :=
begin 
  assume w,
  dsimp [ε_nfa_lang, epsilon_lang],
  constructor,
  {
    assume h,
    cases h with q0 h, cases h with q1 h,
    cases (and.elim_left (and.elim_right h)),
    refl,
    cases ᾰ,
    cases ᾰ,
  },
  {
    assume h,
    let z : fin 1,
      exact 0,
    existsi z, existsi z,
    constructor,
    trivial,
    constructor,
    rw h,
    fconstructor,
    trivial,
  }
end

def single_ε_nfa {Sigma : Type*} [decidable_eq Sigma] (lit : Sigma) : ε_nfa Sigma :=
  {
    Q := fin 2,
    finQ := by apply_instance,
    decQ := by apply_instance,
    inits := λ x , x.val = 0,
    decI := by apply_instance,
    final := λ x , x.val = 1,
    decF := by apply_instance,
    δ := λ q0 x q1 , q0.val = 0 ∧ x = lit ∧ q1.val = 1,
    decD := begin
      assume x,
      dsimp [sigma.uncurry],
      apply_instance,
    end
  }

lemma single_ε_nfa_lang : ∀ x : Sigma, ∀ w : word Sigma, ε_nfa_lang (single_ε_nfa x) w ↔ lit_lang x w :=
begin
  assume x w,
  dsimp [ε_nfa_lang, lit_lang],
  constructor,
  {
    assume h,
    cases h with q0 h, cases h with q1 h,
    cases (and.elim_left (and.elim_right h)),
    {
      cases h with h1 h, cases h with h2 h3,
      have z : q0.val = 0,
        exact h1,
      have f : false,
        have o : q0.val = 1,
          exact h3,
        finish,
      cases f, 
    },
    {
      cases ᾰ with a b, cases b with b c,
      cases b,
      have t: w_1 = [],
      {
        cases ᾰ_1,
        refl,
        cases ᾰ_1_ᾰ,
        have f : false,
          rw c at ᾰ_1_ᾰ_left,
          injection ᾰ_1_ᾰ_left,
        cases f,
        cases ᾰ_1_ᾰ,
        cases (and.elim_left ᾰ_1_ᾰ_right),
      },
      solve_by_elim,
    },
    {
      cases ᾰ,
      cases and.elim_left ᾰ_right,
    }
  },
  {
    assume h,
    let z : fin 2,
      exact 0,
    let o : fin 2,
      exact 1,
    existsi z, existsi o,
    constructor,
    solve_by_elim,
    constructor,
    dsimp [single_ε_nfa],
    rw h,
    fconstructor,
    exact o,
    finish,
    constructor,
    solve_by_elim,
  }
end

def union_ε_nfa {Sigma : Type*} (A : ε_nfa Sigma) (B : ε_nfa Sigma) : ε_nfa Sigma :=
  {
    Q := A.Q ⊕ B.Q,
    finQ := @sum.fintype A.Q B.Q A.finQ B.finQ,
    decQ := @sum.decidable_eq A.Q A.decQ B.Q B.decQ,
    inits := λ q, sum.cases_on q A.inits B.inits,
    decI := begin 
      assume a,
      letI dr := A.decI, letI ds := B.decI,
      cases a;
      tauto,
    end,
    final := λ q, sum.cases_on q A.final B.final,
    decF := begin
      assume a,
      letI dr := A.decF, letI ds := B.decF,
      cases a;
      tauto,
    end,
    δ := λ a x b, match a, b with
      | (sum.inl a), (sum.inl b) := A.δ a x b
      | (sum.inl a), (sum.inr b) := false
      | (sum.inr a), (sum.inl b) := false
      | (sum.inr a), (sum.inr b) := B.δ a x b
      end,
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
        exact A.decD ⟨⟨a, x⟩, b⟩,
        simp at *,
        exact is_false id,
      },
      {
        cases b,
        simp at *,
        exact is_false id,
        simp at *,
        exact B.decD ⟨⟨a, x⟩, b⟩,
      }
    end,
  }

lemma uniform_union : ∀ A B : ε_nfa Sigma, ∀ w : word Sigma, ∀ q0 q1 : A.Q ⊕ B.Q, 
  ε_nfa_δ_star (union_ε_nfa A B) q0 w q1 → (sum.is_left q0 = sum.is_left q1) :=
begin
  assume A B w q0 q1,
  assume h,
  induction h,
  refl,
  rw← h_ih,
  cases h_q0 with aq0 bq0,
  cases h_q1 with aq1 bq1;
  simp,
  cases h_ᾰ,
  cases h_q1 with aq1 bq1,
  simp,
  cases h_ᾰ,
  simp,
  rw← h_ih,
  cases h_q0 with aq0 bq0,
  cases h_q1 with aq1 bq1;
  simp,
  cases h_ᾰ,
  cases h_q1 with aq1 bq1,
  simp,
  cases h_ᾰ,
  simp,
end

lemma left_union : ∀ A B : ε_nfa Sigma, ∀ w : word Sigma, ∀ q0 q1 : A.Q,
  ε_nfa_δ_star (union_ε_nfa A B) (sum.inl q0) w (sum.inl q1) ↔ ε_nfa_δ_star A q0 w q1 :=
  --  ε_nfa_δ_star (union_ε_nfa A B) q0 w q1 ↔ ε_nfa_δ_star A q0 w q1 :=
begin
  assume A B w q0 q1,
  constructor,
  {
    assume h,
    --generalize_hyp e1 : q0 = q0' at h,
    --generalize_hyp e2 : q1 = q1' at h,
    induction h,
    {
      
      fconstructor,
    },
    {
      cases h_q1,
      {
        fconstructor,
        exact h_q1,
        exact h_ᾰ,
        sorry,
      },
      {
        cases h_ᾰ,
      }
    },
    {
      cases q1_1,
      {
        fconstructor,
        exact q1_1,
        exact ᾰ,
        sorry,
      },
      {
        cases h_ᾰ,
      }
    }
  },
  {
    assume h,
    induction h,
    {
      fconstructor,
    },
    {
      fconstructor,
      exact (sum.inl h_q1),
      exact h_ᾰ,
      exact h_ih,
    },
    {
      fconstructor,
      exact (sum.inl h_q1),
      exact h_ᾰ,
      exact h_ih,
    }
  },
end

lemma right_union : ∀ A B : ε_nfa Sigma, ∀ w : word Sigma, ∀ q0 q1 : B.Q,
   ε_nfa_δ_star (union_ε_nfa A B) (sum.inr q0) w (sum.inr q1) ↔ ε_nfa_δ_star B q0 w q1 :=
begin
  assume A B w q0 q1,
  constructor,
  assume h,
  dsimp [union_ε_nfa] at h,
  sorry, 
  sorry,
end

lemma union_ε_nfa_lang : ∀ A B : ε_nfa Sigma, ∀ w : word Sigma, ε_nfa_lang (union_ε_nfa A B) w ↔ union_lang (ε_nfa_lang A) (ε_nfa_lang B) w :=
begin
  assume A B w,
  constructor,
  {
    dsimp [ε_nfa_lang, union_lang],
    assume h,
    cases h with q0 h, cases h with q1 h,
    cases q0,
    {
      left,
      cases q1,
      existsi q0, existsi q1,
      constructor,
      exact (and.elim_left h),
      constructor,
      have g : ε_nfa_δ_star (union_ε_nfa A B) (sum.inl q0) w (sum.inl q1),
        exact (and.elim_left (and.elim_right h)),
      exact (left_union A B w q0 q1).mp g,
      exact (and.elim_right (and.elim_right h)),
      have f : false,
        have g : ε_nfa_δ_star (union_ε_nfa A B) (sum.inl q0) w (sum.inr q1),
          exact (and.elim_left (and.elim_right h)),
        have t := uniform_union A B w (sum.inl q0) (sum.inr q1) g,
          simp at t,
        exact t,
        cases f,
    },
    {
      right,
      cases q1,
      have g : ε_nfa_δ_star (union_ε_nfa A B) (sum.inr q0) w (sum.inl q1),
        exact (and.elim_left (and.elim_right h)),
      have t:= uniform_union A B w (sum.inr q0) (sum.inl q1) g,
        simp at t,
      cases t,
      existsi q0, existsi q1,
      constructor,
      exact (and.elim_left h),
      constructor,
      exact (right_union A B w q0 q1).mp (and.elim_left (and.elim_right h)),
      exact (and.elim_right (and.elim_right h)),
    }   
  },
  {
    dsimp [union_lang, ε_nfa_lang],
    assume h,
    cases h,
    {
      cases h with q0 h, cases h with q1 h,
      existsi (sum.inl q0), existsi (sum.inl q1),
      constructor,
      exact (and.elim_left h),
      constructor,
      exact (left_union A B w q0 q1).mpr (and.elim_left (and.elim_right h)),
      exact (and.elim_right (and.elim_right h)),
    },
    {
      cases h with q0 h, cases h with q1 h,
      existsi (sum.inr q0), existsi (sum.inr q1),
      constructor,
      exact (and.elim_left h),
      constructor,
      exact (right_union A B w q0 q1).mpr (and.elim_left (and.elim_right h)),
      exact (and.elim_right (and.elim_right h)),
    }
  }
end

def star_ε_nfa {Sigma : Type*} [decidable_eq Sigma] (A : ε_nfa Sigma) : ε_nfa Sigma :=
  {
    Q := A.Q,
    finQ := A.finQ,
    decQ := A.decQ,
    inits := A.inits,
    decI := A.decI,
    final := λ q, A.final q ∨ A.inits q,
    decF := begin 
      letI dI := A.decI,
      letI dF := A.decF,
      apply_instance,
    end,
    δ := λ a x b, A.δ a x b ∨ (A.final a ∧ A.inits b ∧ x = none),
    decD := begin
      assume x,
      dsimp [sigma.uncurry],
      cases A.decD ⟨⟨x.fst.fst, x.fst.snd⟩, x.snd⟩ with n y,
      cases A.decF x.fst.fst with nn yy,
      letI not : ¬(A.δ x.fst.fst x.fst.snd x.snd ∨ A.final x.fst.fst ∧ A.inits x.snd ∧ x.fst.snd = none),
        assume h,
        cases h with l r,
        dsimp [sigma.uncurry] at n,
        exact n l,
        apply nn,
        exact and.elim_left r,
      exact is_false not,
      cases A.decI x.snd with nnn yyy,
      letI not : ¬(A.δ x.fst.fst x.fst.snd x.snd ∨ A.final x.fst.fst ∧ A.inits x.snd ∧ x.fst.snd = none),
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
      letI not : ¬(A.δ x.fst.fst x.fst.snd x.snd ∨ A.final x.fst.fst ∧ A.inits x.snd ∧ x.fst.snd = none),
        assume h,
        cases h with l r,
        dsimp [sigma.uncurry] at n,
        exact n l,
        apply h,
        exact and.elim_right (and.elim_right r),
      exact is_false not,
      letI yes : A.δ x.fst.fst x.fst.snd x.snd ∨ A.final x.fst.fst ∧ A.inits x.snd ∧ x.fst.snd = none,
        right,
        exact ⟨yy, ⟨yyy, h⟩⟩,
      exact is_true yes,
      letI yes : A.δ x.fst.fst x.fst.snd x.snd ∨ A.final x.fst.fst ∧ A.inits x.snd ∧ x.fst.snd = none,
        left,
        dsimp [sigma.uncurry] at y,
        exact y,
      exact is_true yes,
    end
  }

def append_ε_nfa {Sigma : Type*} [decidable_eq Sigma] (A : ε_nfa Sigma) (B : ε_nfa Sigma) : ε_nfa Sigma :=
  {
    Q := A.Q ⊕ B.Q,
    finQ := @sum.fintype A.Q B.Q A.finQ B.finQ,
    decQ := @sum.decidable_eq A.Q A.decQ B.Q B.decQ,
    inits := λ q, sum.cases_on q A.inits (λ _, false),
    decI := begin
      assume a,
      cases a;
      simp at *,
      exact A.decI a,
      exact is_false id,
    end,
    final := λ q, sum.cases_on q (λ _, false) B.final,
    decF := begin
      assume a,
      cases a;
      simp at *,
      exact is_false id,
      exact B.decF a,
    end,
    δ := λ a x b, match a, b with
        | (sum.inl a), (sum.inl b) := A.δ a x b
        | (sum.inl a), (sum.inr b) := A.final a ∧ B.inits b ∧ x = none
        | (sum.inr a), (sum.inl b) := false
        | (sum.inr a), (sum.inr b) := B.δ a x b
      end,
    decD := begin
      assume a,
      cases a with ax b, cases ax with a x,
      cases a; cases b; dsimp [sigma.uncurry],
      exact A.decD ⟨⟨a, x⟩, b⟩,
      {
        letI dF := A.decF,
        letI dI := B.decI,
        letI deq := @sum.decidable_eq A.Q A.decQ B.Q B.decQ,
        apply_instance,
      },
      exact is_false id,
      exact B.decD ⟨⟨a, x⟩, b⟩,
    end,
  }

lemma append_lemma : ∀ A : ε_nfa Sigma, ∀ u v : word Sigma, ∀ q0 q1 q2 q3 : A.Q, 
  ε_nfa_δ_star A q0 u q2 ∧ ε_nfa_δ_star A q3 v q1 ∧ A.δ q2 none q3 →
  ε_nfa_δ_star A q0 (u ++ v) q1 :=
begin
  sorry,
end

lemma append_ε_nfa_lang : ∀ A B : ε_nfa Sigma, ∀ w : word Sigma, ε_nfa_lang (append_ε_nfa A B) w ↔ append_lang (ε_nfa_lang A) (ε_nfa_lang B) w :=
begin
  assume A B w,
  constructor,
  {
    dsimp [ε_nfa_lang, append_lang],
    assume h,
    cases h with q0 h, cases h with q1 h,
    --dsimp [append_ε_nfa] at h,
    cases h with h1 h, cases h with h2 h3,
    cases q0,
    {
      cases q1,
      {
        cases h3,
      },
      {
        have delimiter : ∃ q2 : A.Q, ∃ q3 : B.Q, ∃ u v : word Sigma,
          ε_nfa_δ_star A q0 u q2
          ∧ ε_nfa_δ_star B q3 v q1
          ∧ (append_ε_nfa A B).δ (sum.inl q2) none (sum.inr q3)
          ∧ w = u ++ v,
        sorry,
        cases delimiter with q2 h4, cases h4 with q3 h4,
        cases h4 with u h4, cases h4 with v h4,
        cases h4 with h4 h5, cases h5 with h5 h6, cases h6 with h6 h7,
        existsi u, existsi v,
        constructor,
        {
          existsi q0, existsi q2,
          constructor, exact h1,
          constructor, exact h4,
          exact (and.elim_left h6),
        },
        {
          constructor,
          {
            existsi q3, existsi q1,
            constructor,
            exact (and.elim_left (and.elim_right h6)),
            constructor, exact h5, exact h3,
          },
          exact h7,
        }
      }
    },
    {
      cases h1,
    }
  },
  {
    dsimp [ε_nfa_lang, append_lang],
    assume h,
    cases h with u h, cases h with v h,
    cases h with h1 h2, cases h2 with h2 h3,
    cases h1 with q0 h1, cases h1 with q2 h1,
    cases h2 with q3 h2, cases h2 with q1 h2,
    existsi (sum.inl q0), existsi (sum.inr q1),
    constructor, exact (and.elim_left h1),
    constructor, 
    {
      rw h3,
      apply append_lemma (append_ε_nfa A B) u v (sum.inl q0) (sum.inr q1) (sum.inl q2) (sum.inr q3),
      sorry,
    },
    exact (and.elim_right (and.elim_right h2)),

  }
end

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
  cases r,
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
    dsimp [re_lang],
    dsimp [re2ε_nfa],
    let g := (iff.symm (union_ε_nfa_lang (re2ε_nfa r_ᾰ) (re2ε_nfa r_ᾰ_1) w)),
    let h : union_lang (re_lang r_ᾰ) (re_lang r_ᾰ_1) w ↔ union_lang (ε_nfa_lang (re2ε_nfa r_ᾰ)) (ε_nfa_lang (re2ε_nfa r_ᾰ_1)) w,
      sorry,
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
    induction w,
    constructor;
    {
      dsimp [re_lang, ε_nfa_lang],
      assume h,
      sorry,
    },
    sorry,
  },
  {
    -- append
    assume w,
    dsimp [re_lang, ε_nfa_lang],
    constructor,
    {
      assume h,
      dsimp [append_lang] at h,
      cases h with u h1, cases h1 with v h2,
      dsimp [re2ε_nfa],
      cases h2 with h3 h4,
      cases h4 with h5 h6,
      sorry,
    },
    {
      assume h,
      cases h with q0 h,
      cases h with q1 h,
      dsimp [append_lang],
      sorry,
    }
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


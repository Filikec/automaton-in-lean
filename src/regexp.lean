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


lemma left_union' : ∀ A B : ε_nfa Sigma, ∀ w : word Sigma, ∀ q0' q1' : A.Q, 
  ε_nfa_δ_star A q0' w q1' → ε_nfa_δ_star (union_ε_nfa A B) (sum.inl q0') w (sum.inl q1') :=
begin
  assume A B w q0' q1' h,
  induction h,
  case ε_nfa_δ_star.empty : q 
  {
    constructor,
  },
  case ε_nfa_δ_star.step : q0 q1 q2 x w h0 h1 ih 
  {
    fconstructor,
    exact (sum.inl q1),
    exact h0,
    exact ih,
  },
  case ε_nfa_δ_star.epsilon : q0 q1 q2 w h0 h1 ih
  {
    fconstructor,
    exact (sum.inl q1),
    exact h0,
    exact ih,
  }
end

lemma right_union' : ∀ A B : ε_nfa Sigma, ∀ w : word Sigma, ∀ q0' q1' : B.Q, 
  ε_nfa_δ_star B q0' w q1' → ε_nfa_δ_star (union_ε_nfa A B) (sum.inr q0') w (sum.inr q1') :=
begin
  assume A B w q0' q1' h,
  induction h,
  case ε_nfa_δ_star.empty : q 
  {
    constructor,
  },
  case ε_nfa_δ_star.step : q0 q1 q2 x w h0 h1 ih 
  {
    fconstructor,
    exact (sum.inr q1),
    exact h0,
    exact ih,
  },
  case ε_nfa_δ_star.epsilon : q0 q1 q2 w h0 h1 ih
  {
    fconstructor,
    exact (sum.inr q1),
    exact h0,
    exact ih,
  }
end

lemma union_lem : ∀ A B : ε_nfa Sigma, ∀ w : word Sigma, ∀ q0 q1 : (union_ε_nfa A B).Q,
  ε_nfa_δ_star (union_ε_nfa A B) q0 w q1 ↔ 
    (∃ q0' q1' : A.Q, q0 = sum.inl q0' ∧ q1 = sum.inl q1' ∧ ε_nfa_δ_star A q0' w q1')
    ∨
    (∃ q0' q1' : B.Q, q0 = sum.inr q0' ∧ q1 = sum.inr q1' ∧ ε_nfa_δ_star B q0' w q1')
    :=
begin
  assume A B w q0 q1,
  constructor,
  {
    assume h,
    induction h,
    case ε_nfa_δ_star.empty : q 
    {
      cases q,
      {  
        left,
        existsi [q, q],
        have empty_construct: ε_nfa_δ_star A q list.nil q,
          constructor,
        exact and.intro (refl $ sum.inl q) (and.intro (refl $ sum.inl q) empty_construct),
      },
      {
        right,
        existsi [q, q],
        have empty_construct: ε_nfa_δ_star B q list.nil q,
          constructor,
        exact and.intro (refl $ sum.inr q) (and.intro (refl $ sum.inr q) empty_construct),
      }
    }, 
    case ε_nfa_δ_star.step : q00 q11 q22 x w h0 h1 ih
    {
      cases q00,
      {
        cases q11,
        {
          left,
          cases ih,
          {
            cases ih with q00' ih, cases ih with q11' ih,
            existsi [q00, q11'],
            constructor, refl,
            constructor, exact (and.elim_left (and.elim_right ih)),
            fconstructor,
            exact q11,
            exact h0,
            have eq : q11 = q00',
              injection (and.elim_left ih),
            rw eq,
            exact (and.elim_right (and.elim_right ih)),
          },
          {
            cases ih with q0' ih, cases ih with q1' ih,
            rw (and.elim_left ih) at h0,
            cases h0,
          },
        },
        {
          cases h0,
        }
      },
      {
        cases q11,
        {
          cases h0,
        },
        {
          right,
          cases ih,
          {
            cases ih with q0' ih, cases ih with q1' ih,
            rw (and.elim_left ih) at h0,
            cases h0, 
          },
          {
            cases ih with q00' ih, cases ih with q11' ih,
            existsi [q00, q11'],
            constructor, refl,
            constructor, exact (and.elim_left (and.elim_right ih)),
            fconstructor,
            exact q11,
            exact h0,
            have eq : q11 = q00',
              injection (and.elim_left ih),
            rw eq,
            exact (and.elim_right (and.elim_right ih)),
          }
        }
      }
    },
    case ε_nfa_δ_star.epsilon : q00 q11 q22 w h0 h1 ih
    {
      cases q00,
      {
        cases q11,
        {
          left,
          cases ih,
          {
            cases ih with q00' ih, cases ih with q11' ih,
            existsi [q00, q11'],
            constructor, refl,
            constructor, exact (and.elim_left (and.elim_right ih)),
            fconstructor,
            exact q11,
            exact h0,
            have eq : q11 = q00',
              injection (and.elim_left ih),
            rw← eq at ih,
            exact (and.elim_right (and.elim_right ih)),
          },
          {
            cases ih with q0' ih, cases ih with q1' ih,
            rw (and.elim_left ih) at h0,
            cases h0,
          }
        },
        {
          cases h0,
        }
      },
      {
        cases q11,
        {
          cases h0,
        },
        {
          right,
          cases ih,
          {
            cases ih with q0' ih, cases ih with q1' ih,
            rw (and.elim_left ih) at h0,
            cases h0,
          },
          {
            cases ih with q00' ih, cases ih with q11' ih,
            existsi [q00, q11'],
            constructor, refl,
            constructor, exact (and.elim_left (and.elim_right ih)),
            fconstructor,
            exact q11,
            exact h0,
            have eq : q11 = q00',
              injection (and.elim_left ih),
            rw← eq at ih,
            exact (and.elim_right (and.elim_right ih)),
          }
        }
      }
    },
  },
  {
    assume h,
    cases h with hA hB,
    {
      cases hA with q0' hA, cases hA with q1' hA,
      cases hA with h0 hA, cases hA with h1 hA,
      have left_union: ε_nfa_δ_star (union_ε_nfa A B) (sum.inl q0') w (sum.inl q1'),
        apply (left_union' A B w q0' q1' hA),
      rw← h0 at left_union,
      rw← h1 at left_union,
      exact left_union,
    },
    {
      cases hB with q0' hB, cases hB with q1' hB,
      cases hB with h0 hB, cases hB with h1 hB,
      have right_union: ε_nfa_δ_star (union_ε_nfa A B) (sum.inr q0') w (sum.inr q1'),
        apply (right_union' A B w q0' q1' hB),
      rw← h0 at right_union,
      rw← h1 at right_union,
      exact right_union,
    }
  }
end

lemma left_union : ∀ A B : ε_nfa Sigma, ∀ w : word Sigma, ∀ q0 q1 : A.Q,
  ε_nfa_δ_star (union_ε_nfa A B) (sum.inl q0) w (sum.inl q1) ↔ ε_nfa_δ_star A q0 w q1 :=
begin
  assume A B w q0 q1,
  constructor,
  {
    assume h,
    have h1 := iff.mp (union_lem A B w (sum.inl q0) (sum.inl q1)),
    cases h1 h with h1 h1,
    {
      cases h1 with q0' h1, cases h1 with q1' h1,
      cases h1 with h1 h2, cases h2 with h2 h3,
      injections_and_clear,
      rw← h_1 at h3,
      rw← h_2 at h3,
      exact h3,
    },
    {
      cases h1 with q0' h1, cases h1 with q1' h1,
      cases (and.elim_left h1),
    }
  },
  {
    assume h,
    have h1 := iff.mpr (union_lem A B w (sum.inl q0) (sum.inl q1)),
    apply h1,
    left,
    existsi [q0, q1],
    constructor, refl,
    constructor, refl,
    exact h,
  },
end

lemma right_union : ∀ A B : ε_nfa Sigma, ∀ w : word Sigma, ∀ q0 q1 : B.Q,
   ε_nfa_δ_star (union_ε_nfa A B) (sum.inr q0) w (sum.inr q1) ↔ ε_nfa_δ_star B q0 w q1 :=
begin
  assume A B w q0 q1,
  constructor,
  {
    assume h,
    have h1 := iff.mp (union_lem A B w (sum.inr q0) (sum.inr q1)),
    cases h1 h with h1 h1,
    {
      cases h1 with q0' h1, cases h1 with q1' h1,
      cases (and.elim_left h1),
    },
    {
      cases h1 with q0' h1, cases h1 with q1' h1,
      cases h1 with h1 h2, cases h2 with h2 h3,
      injections_and_clear,
      rw← h_1 at h3,
      rw← h_2 at h3,
      exact h3,
    },
  },
  {
    assume h,
    have h1 := iff.mpr (union_lem A B w (sum.inr q0) (sum.inr q1)),
    apply h1,
    right,
    existsi [q0, q1],
    constructor, refl,
    constructor, refl,
    exact h,
  },
end

lemma union_ε_nfa_lang : ∀ A B : ε_nfa Sigma, ∀ w : word Sigma,
  ε_nfa_lang (union_ε_nfa A B) w ↔ union_lang (ε_nfa_lang A) (ε_nfa_lang B) w :=
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

lemma star_lem : ∀ A : ε_nfa Sigma, ∀ w : word Sigma, ∀ q0 q1 : (star_ε_nfa A).Q,
  ε_nfa_δ_star (star_ε_nfa A) q0 w q1 ∧ A.final q1 →
    (∃ v r : word Sigma, 
      w = v ++ r 
      ∧ star_lang (ε_nfa_lang A) r
      ∧ ∃ q2 : (star_ε_nfa A).Q, ε_nfa_δ_star A q0 v q2 ∧ A.final q2)
    ∨ (A.inits q0 ∧ w = [] ∧ q0 = q1) :=
begin
  assume A w q0 q1 h,
  cases h with Astar Afinal,
  induction Astar,
  case ε_nfa_δ_star.empty : q
  {
    sorry,
  },
  case ε_nfa_δ_star.step : q00 q11 q22 x w h0 h1 ih
  {
    cases (ih Afinal) with extend empty,
    {
      left,
      cases extend with v ih, cases ih with r ih,
      cases ih with wvr ih, cases ih with langStar ih,
      cases ih with q2' ih, cases ih with Astar finalq2',
      existsi [(x :: v), r],
      rw wvr, simp, constructor, exact langStar,
      existsi q2', constructor,
      {
        fconstructor,
        exact q11, cases h0, exact h0, cases (and.elim_right $ and.elim_right $ h0),
        exact Astar,
      },
      exact finalq2',
    },
    {
      left,
      cases empty with initq11 ih, cases ih with wnil q1122,
      existsi [[x], []], simp, constructor, exact wnil,
      constructor, constructor,
      existsi q11,
      constructor,
      {
        fconstructor,
        exact q11,
        cases h0, exact h0, cases (and.elim_right $ and.elim_right $ h0),
        constructor,
      },
      rw q1122, exact Afinal,
    },
  },
  case ε_nfa_δ_star.epsilon : q00 q11 q22 w h0 h1 ih
  {
    cases (ih Afinal) with extend empty,
    {
      cases extend with v ih, cases ih with r ih,
      cases ih with wvr ih, cases ih with langStar ih,
      cases ih with q2' ih, cases ih with Astar finalq2',
      cases h0,
      {
        left,
        existsi [v, r],
        constructor, exact wvr,
        constructor, exact langStar,
        existsi q2',
        constructor,
        {
          fconstructor,
          exact q11, exact h0, exact Astar,
        },
        exact finalq2',
      },
      {
        left,
        existsi [v, r],
        constructor, exact wvr,
        constructor, exact langStar,
        existsi q2',
        constructor,
        {
          fconstructor,
          exact q11,
          sorry, sorry,
        },
        sorry,
      }
    },
    {
      cases h0,
      sorry, sorry,
    }
  },
end

lemma star_ε_nfa_lang : ∀ A : ε_nfa Sigma, ∀ w : word Sigma,
  ε_nfa_lang (star_ε_nfa A) w ↔ star_lang (ε_nfa_lang A) w :=
begin
  assume A w,
  constructor,
  {
    assume h,
    dsimp [ε_nfa_lang] at h,
    cases h with q0 h, cases h with q1 h,
    cases h with init h, cases h with star final,
    induction star,
    case ε_nfa_δ_star.empty : q
    {
     constructor,
    },
    case ε_nfa_δ_star.step : q00 q11 q22 x w h0 h1 ih
    {
      sorry,
    },
    sorry,
  },
  {
    assume h,
    dsimp [ε_nfa_lang],
    induction h,
    sorry,
    sorry,
  }
end

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
        unfold_aux,
        apply_instance,
      },
      exact is_false id,
      exact B.decD ⟨⟨a, x⟩, b⟩,
    end,
  }

lemma left_append : ∀ A B : ε_nfa Sigma, ∀ w : word Sigma, ∀ q0 q1 : A.Q,
  ε_nfa_δ_star A q0 w q1 → ε_nfa_δ_star (append_ε_nfa A B) (sum.inl q0) w (sum.inl q1) :=
begin
  assume A B w q0 q1 h,
  induction h,
  case ε_nfa_δ_star.empty : q
  {
    constructor,
  },
  case ε_nfa_δ_star.step : q11 q22 q33 x w h1 h2 ih
  {
    fconstructor,
    exact (sum.inl q22),
    exact h1,
    exact ih,
  },
  case ε_nfa_δ_star.epsilon : q11 q22 q33 w h1 h2 ih
  {
    fconstructor,
    exact (sum.inl q22),
    exact h1,
    exact ih,
  }
end

lemma right_append : ∀ A B : ε_nfa Sigma, ∀ w : word Sigma, ∀ q0 q1 : B.Q,
  ε_nfa_δ_star B q0 w q1 → ε_nfa_δ_star (append_ε_nfa A B) (sum.inr q0) w (sum.inr q1) :=
begin
  assume A B w q0 q1 h,
  induction h,
  case ε_nfa_δ_star.empty : q
  {
    constructor,
  },
  case ε_nfa_δ_star.step : q11 q22 q33 x w h1 h2 ih
  {
    fconstructor,
    exact (sum.inr q22),
    exact h1,
    exact ih,
  },
  case ε_nfa_δ_star.epsilon : q11 q22 q33 w h1 h2 ih
  {
    fconstructor,
    exact (sum.inr q22),
    exact h1,
    exact ih,
  }
end

lemma append_lemᵣ : ∀ A B : ε_nfa Sigma, ∀ u v : word Sigma, ∀ q0 : A.Q, ∀ q1 : B.Q, 
  (∃ q2 : A.Q, ∃ q3 : B.Q, A.final q2 ∧ B.inits q3
   ∧ ε_nfa_δ_star A q0 u q2 ∧ ε_nfa_δ_star B q3 v q1) →
  ε_nfa_δ_star (append_ε_nfa A B) (sum.inl q0) (u ++ v) (sum.inr q1) :=
begin
  assume A B u v q0 q1 h,
  cases h with q2 h, cases h with q3 h,
  cases h with Afinal h, cases h with Binits h,
  cases h with Astar Bstar,
  have a2b : (append_ε_nfa A B).δ (sum.inl q2) none (sum.inr q3),
  {
    constructor, exact Afinal,
    constructor, exact Binits,
    refl,
  },
  induction Astar, 
  case ε_nfa_δ_star.empty : q
  {
    simp,fconstructor,
    exact (sum.inr q3),
    exact a2b, exact right_append A B v q3 q1 Bstar,
  },
  case ε_nfa_δ_star.step : q00 q11 q22 x w h1 h2 ih
  {
    fconstructor,
    exact sum.inl q11,
    exact h1,
    apply ih,
    exact Afinal,
    exact a2b,
  },
  case ε_nfa_δ_star.epsilon : q00 q11 q22 w h1 h2 ih
  {
    fconstructor,
    exact sum.inl q11,
    exact h1,
    apply ih,
    exact Afinal,
    exact a2b,
  }
end

lemma append_lem : ∀ A B : ε_nfa Sigma, ∀ w : word Sigma, ∀ q0 q1 : (append_ε_nfa A B).Q,
  ε_nfa_δ_star (append_ε_nfa A B) q0 w q1 →
  (∃ q0' : A.Q, ∃ q1' : B.Q, q0 = sum.inl q0' ∧ q1 = sum.inr q1' 
   ∧ ∃ u v : word Sigma, ∃ q2' : A.Q, ∃ q3' : B.Q, A.final q2' ∧ B.inits q3'
   ∧ ε_nfa_δ_star A q0' u q2' ∧ ε_nfa_δ_star B q3' v q1'
   ∧ u ++ v = w)
  ∨ (∃ q0' q1' : A.Q, q0 = sum.inl q0' ∧ q1 = sum.inl q1'
     ∧ ε_nfa_δ_star A q0' w q1')
  ∨ (∃ q0' q1' : B.Q, q0 = sum.inr q0' ∧ q1 = sum.inr q1'
     ∧ ε_nfa_δ_star B q0' w q1') :=
begin
  assume A B w q0 q1 h,
  induction h,
  case ε_nfa_δ_star.empty : q
  {
    cases q,
    right, left, existsi [q, q],
    simp, constructor,
    right, right, existsi [q, q],
    simp, constructor,
  },
  case ε_nfa_δ_star.step : q00 q11 q22 x w h1 h2 ih
  {
    cases q00,
    {
      cases q11,
      {
        cases ih,
        {
          left,
          cases ih with q0' ih, cases ih with q1' ih,
          cases ih with eq1 ih, cases ih with eq2 ih,
          cases ih with u ih, cases ih with v ih,
          cases ih with q2' ih, cases ih with q3 ih,
          cases ih with Afinal ih, cases ih with Binits ih,
          cases ih with Astar ih, cases ih with Bstar split_eq,
          existsi [q00, q1'], constructor, refl,
          constructor, exact eq2, 
          existsi [(x :: u), v],
          existsi [q2', q3],
          constructor, exact Afinal,
          constructor, exact Binits,
          constructor,
          {
            fconstructor,
            exact q11, exact h1,
            injection eq1 with eq1, rw eq1,
            exact Astar,
          },
          constructor,
          {
            exact Bstar,
          },
          {
            rw← split_eq,
            exact list.cons_append x u v,
          }
        },
        {
          cases ih,
          {
            right, left,
            cases ih with q0' ih, cases ih with q1' ih,
            existsi [q00, q1'],
            cases ih with eq1 ih, cases ih with eq2 Astar,
            simp, constructor, exact eq2,
            fconstructor,
            exact q11, exact h1,
            injection eq1 with eq1, rw eq1, exact Astar,
          },
          {
            cases ih with q0' ih, cases ih with q1' ih,
            cases ih with f _, cases f,
          }
        }
      },
      {
        cases h1 with _ h1, cases h1 with _ f, cases f,
      }
    },
    {
      cases q11,
      {
        cases h1,
      },
      {
        cases ih,
        {
          cases ih with q0' ih, cases ih with q1' ih,
          cases ih with f _, cases f,
        },
        {
          cases ih,
          {
            cases ih with q0' ih, cases ih with q1' ih,
            cases ih with f _, cases f,
          },
          {
            right, right,
            cases ih with q0' ih, cases ih with q1' ih,
            cases ih with eq1 ih, cases ih with eq2 Bstar,
            existsi [q00, q1'],
            simp, constructor, exact eq2,
            fconstructor,
            exact q11,
            exact h1, injection eq1 with eq1, rw eq1,
            exact Bstar,
          }
        },
      }
    },
  },
  case ε_nfa_δ_star.epsilon : q00 q11 q22 w h1 h2 ih
  {
    cases q00,
    {
      cases q11,
      {
        cases ih,
        {
          left,
          cases ih with q0' ih, cases ih with q1' ih,
          cases ih with eq1 ih, cases ih with eq2 ih,
          cases ih with u ih, cases ih with v ih,
          cases ih with q2' ih, cases ih with q3 ih,
          cases ih with Afinal ih, cases ih with Binits ih,
          cases ih with Astar ih, cases ih with Bstar split_eq,
          existsi [q00, q1'], constructor, refl,
          constructor, exact eq2, 
          existsi [u, v],
          existsi [q2', q3],
          constructor, exact Afinal,
          constructor, exact Binits,
          constructor,
          {
            fconstructor,
            exact q11, exact h1,
            injection eq1 with eq1, rw eq1,
            exact Astar,
          },
          constructor,
          {
            exact Bstar,
          },
          {
            rw← split_eq,
          }
        },
        {
          cases ih,
          {
            right, left,
            cases ih with q0' ih, cases ih with q1' ih,
            existsi [q00, q1'],
            cases ih with eq1 ih, cases ih with eq2 Astar,
            simp, constructor, exact eq2,
            fconstructor,
            exact q11, exact h1,
            injection eq1 with eq1, rw eq1, exact Astar,
          },
          {
            cases ih with q0' ih, cases ih with q1' ih,
            cases ih with f _, cases f,
          }
        }
      },
      {
        left, 
        cases ih,
        {
          cases ih with q0' ih, cases ih with q1' ih,
          cases ih with f _, cases f,
        },
        cases ih,
        {
          cases ih with q0' ih, cases ih with q1' ih,
          cases ih with f _, cases f,
        },
        {
          cases h1 with Afinal h1, cases h1 with Binits _,
          cases ih with q0' ih, cases ih with q1' ih,
          cases ih with eq1 ih, cases ih with eq2 Bstar,
          existsi [q00, q1'],
          constructor, refl,
          constructor, exact eq2,
          existsi [[], w, q00, q11],
          constructor, exact Afinal,
          constructor, exact Binits,
          constructor, constructor,
          constructor, injection eq1 with eq1, rw eq1, exact Bstar,
          exact list.nil_append w,
        }
      }
    },
    {
      cases q11,
      {
        cases h1,
      },
      {
        cases ih,
        {
          cases ih with q0' ih, cases ih with q1' ih,
          cases ih with f _, cases f,
        },
        {
          cases ih,
          {
            cases ih with q0' ih, cases ih with q1' ih,
            cases ih with f _, cases f,
          },
          {
            right, right,
            cases ih with q0' ih, cases ih with q1' ih,
            cases ih with eq1 ih, cases ih with eq2 Bstar,
            existsi [q00, q1'],
            simp, constructor, exact eq2,
            fconstructor,
            exact q11,
            exact h1, injection eq1 with eq1, rw eq1,
            exact Bstar,
          }
        },
      }
    },
  },
end

lemma append_ε_nfa_lang : ∀ A B : ε_nfa Sigma, ∀ w : word Sigma,
  ε_nfa_lang (append_ε_nfa A B) w ↔ append_lang (ε_nfa_lang A) (ε_nfa_lang B) w :=
begin
  assume A B w,
  constructor,
  {
    dsimp [ε_nfa_lang, append_lang],
    assume h,
    cases h with q0 h, cases h with q1 h,
    cases h with h1 h, cases h with h2 h3,
    have g := append_lem A B w q0 q1 h2,
    cases g,
    {
      cases g with q0' g, cases g with q1' g,
      cases g with eq1 g, cases g with eq2 g,
      cases g with u g, cases g with v g,
      cases g with q2' g, cases g with q3' g,
      cases g with Afinal g, cases g with Binits ih,
      cases ih with Astar g, cases g with Bstar split_eq,
      existsi [u, v],
      constructor,
      {
        existsi [q0', q2'],
        constructor, finish,
        constructor, exact Astar, exact Afinal,
      },
      constructor,
      {
        existsi [q3', q1'],
        constructor, exact Binits,
        constructor, exact Bstar, finish,
      },
      exact eq.symm split_eq,
    },
    cases g,
    {
      cases g with q0' g, cases g with q1' g,
      cases g with eq1 g, cases g with eq2 Astar,
      existsi [w, []],
      rw eq2 at h3, cases h3,
    },
    {
      cases g with q0' g, cases g with q1' g,
      cases g with eq1 g, cases g with eq2 Astar,
      rw eq1 at h1, cases h1,
    }
  },
  {
    dsimp [ε_nfa_lang, append_lang],
    assume h,
    cases h with u h, cases h with v h,
    cases h with h1 h2, cases h2 with h2 h3,
    cases h1 with q0 h1, cases h1 with q2 h1,
    cases h2 with q3 h2, cases h2 with q1 h2,
    existsi [sum.inl q0, sum.inr q1],
    constructor, exact (and.elim_left h1),
    constructor, 
    {
      let h11 : ε_nfa_δ_star A q0 u q2, exact (and.elim_left $ and.elim_right $ h1),
      let h22 : ε_nfa_δ_star B q3 v q1, exact (and.elim_left $ and.elim_right $ h2),
      rw h3,
      apply append_lemᵣ A B u v q0 q1,
      existsi [q2, q3],
      constructor, exact (and.elim_right $ and.elim_right $ h1),
      constructor, exact (and.elim_left h2),
      constructor, exact h11,
      exact h22,
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


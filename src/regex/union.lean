import data.fin.basic
import data.fintype.basic
import data.list
import ..automata_typeclass

variables {Sigma : Type} [decidable_eq Sigma]

def union_lang (P Q : lang Sigma) : lang Sigma 
:= λ w , P w ∨ Q w 

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
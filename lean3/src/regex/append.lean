import data.fin.basic
import data.fintype.basic
import data.list
import ..automata_typeclass

variables {Sigma : Type} [decidable_eq Sigma]

def append_lang (P Q : lang Sigma) : lang Sigma 
:= λ w, ∃ u v : word Sigma, P u ∧ Q v ∧ w = u ++ v    

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
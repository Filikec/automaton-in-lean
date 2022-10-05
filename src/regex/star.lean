import data.fin.basic
import data.fintype.basic
import data.list
import ..automata_typeclass

variables {Sigma : Type} [decidable_eq Sigma]

inductive star_lang (P : lang Sigma) : lang Sigma 
| empty_star : star_lang []
| extend : ∀ u w, P u → star_lang w 
    → star_lang (u ++ w) 

def star_ε_nfa {Sigma : Type*} [decidable_eq Sigma] (A : ε_nfa Sigma) : ε_nfa Sigma :=
  {
    Q := A.Q ⊕ fin 2,
    finQ := @sum.fintype A.Q (fin 2) A.finQ (fin.fintype 2),
    decQ := @sum.decidable_eq A.Q A.decQ (fin 2) (fin.decidable_eq 2),
    inits := λ q, q = sum.inr 0,
    decI := begin
      assume a,
      cases a with q z,
      have f : ¬(λ (q : A.Q ⊕ fin 2), q = sum.inr 0) (sum.inl q),
      {
        assume h, cases h,
      },
      exact is_false f,
      unfold_coes, simp at *,
      have t := fin.decidable_eq 2,
      dsimp [decidable_eq] at t,
      dsimp [decidable_rel] at t,
      solve_by_elim,
    end,
    final := λ q, q = sum.inr 1,
    decF := begin
      assume a,
      cases a with q z,
      have f : ¬(λ (q : A.Q ⊕ fin 2), q = sum.inr 1) (sum.inl q),
      {
        assume h, cases h,
      },
      exact is_false f,
      unfold_coes, simp at *,
      have t:= fin.decidable_eq 2,
      dsimp [decidable_eq, decidable_rel] at t,
      solve_by_elim,
    end, 
    δ := λ a x b, match a, x, b with
          | (sum.inl a), x, (sum.inl b) := A.δ a x b ∨ A.final a ∧ x = none ∧ A.inits b
          | (sum.inr a), x, (sum.inl b) := x = none ∧ A.inits b ∧ a = 0
          | (sum.inl a), x, (sum.inr b) := x = none ∧ A.final a ∧ b = 1
          | (sum.inr a), x, (sum.inr b) := x = none ∧ a = 0 ∧ b = 1
        end,
    decD := begin
      assume a,
      cases a with ax b, cases ax with a x,
      cases a; cases b; dsimp [sigma.uncurry],
      {
        letI dF := A.decF,
        letI decQ := @sum.decidable_eq A.Q A.decQ (fin 2) (fin.decidable_eq 2),
        letI dI := A.decI,
        letI dD := A.decD,
        unfold_aux,
        cases dD ⟨⟨a, x⟩, b⟩,
        {
          cases dF a with n y,
          {
            have f : ¬(A.δ a x b ∨ A.final a ∧ x = none ∧ A.inits b),
              assume nn, cases nn, dsimp [sigma.uncurry] at h,
              exact h nn,
              exact n (and.elim_left nn),
            exact is_false f,
          },
          {
            have eq := @option.decidable_eq_none Sigma x,
            cases eq,
            have f : ¬(A.δ a x b ∨ A.final a ∧ x = none ∧ A.inits b),
              assume nn, cases nn, dsimp [sigma.uncurry] at h,
              exact h nn, exact eq (and.elim_left $ and.elim_right $ nn),
            exact is_false f,
            cases dI b with n2 y2,
            have f : ¬(A.δ a x b ∨ A.final a ∧ x = none ∧ A.inits b),
              assume nn, cases nn, dsimp [sigma.uncurry] at h,
              exact h nn, exact n2 (and.elim_right $ and.elim_right $ nn),
            exact is_false f,
            have t : (A.δ a x b ∨ A.final a ∧ x = none ∧ A.inits b),
              right, constructor, exact y, constructor, exact eq, exact y2,
            exact is_true t,
          }
        },
        {
          have t : (A.δ a x b ∨ A.final a ∧ x = none ∧ A.inits b),
            left, dsimp [sigma.uncurry] at h, exact h,
          exact is_true t,
        }
      },
      {
        letI dF := A.decF,
        letI decQ := @sum.decidable_eq A.Q A.decQ (fin 2) (fin.decidable_eq 2),
        unfold_aux,
        apply_instance,
      },
      {
        letI dI := A.decI,
        letI decQ := @sum.decidable_eq A.Q A.decQ (fin 2) (fin.decidable_eq 2),
        unfold_aux,
        apply_instance,
      },
      {
        letI decQ := @sum.decidable_eq A.Q A.decQ (fin 2) (fin.decidable_eq 2),
        unfold_aux,
        apply_instance,
      }
    end
  }

def state_lang (A : ε_nfa Sigma) : A.Q → lang Sigma :=
  λ q w, ∃ q' : A.Q, ε_nfa_δ_star A q w q' ∧ A.final q'

def lang1 (A : ε_nfa Sigma) : lang Sigma :=
  λ r , ∃ q : A.Q, A.inits q ∧ state_lang A q r

lemma star_lem : ∀ A : ε_nfa Sigma, ∀ q0 q1 : (star_ε_nfa A).Q, ∀ w : word Sigma,
  ε_nfa_δ_star (star_ε_nfa A) q0 w q1 ∧ (star_ε_nfa A).final q1 → 
  (w = [] ∧ (q0 = sum.inr 1 ∨ q0 = sum.inr 0 ∨ ∃ q0' : A.Q, q0 = sum.inl q0' ∧ A.final q0'))
  ∨ (q0 = sum.inr 0 ∧ ∃ v r : word Sigma, w = v ++ r ∧ ε_nfa_lang A v ∧ star_lang (ε_nfa_lang A) r)
  ∨ (∃ q0' : A.Q, q0 = sum.inl q0' ∧ A.final q0' ∧ ∃ v r : word Sigma, w = v ++ r ∧ ε_nfa_lang A v ∧ star_lang (ε_nfa_lang A) r)
  ∨ (∃ q0' : A.Q, q0 = sum.inl q0' ∧ ∃ v r : word Sigma, w = v ++ r ∧ ∃ q1' : A.Q, A.final q1' ∧ ε_nfa_δ_star A q0' v q1' ∧ star_lang (ε_nfa_lang A) r)
:=
begin
  assume A q0 q1 w h,
  cases h with h Afinal,
  induction h,
  case ε_nfa_δ_star.empty : q
  {
    left, simp, left, cases Afinal, refl,
  },
  case ε_nfa_δ_star.step : q00 q11 q22 x w h0 h1 ih
  {
    have ih := ih Afinal,
    cases ih with ih ih,
    {
      cases ih with wnil ih,
      cases ih with tofinal ih,
      {
        simp, right,
        rw wnil at *, rw tofinal at *,
        cases h1; cases q00,
        repeat {
          cases h0 with f _, cases f,
        },
      },
      cases ih with fromstart Afinal,
      {
        cases Afinal,
        rw fromstart at *,
        simp,
        cases q00, repeat {cases h0 with f _, cases f},
      },
      {
        rw wnil, simp,
        right, right,
        cases q00,
        {
          existsi q00, simp,
          existsi [[x], []], simp,
          cases Afinal with q1' Afinal,
          existsi q1',
          constructor, exact (and.elim_right Afinal),
          constructor,
          {
            fconstructor,
            exact q1', rw (and.elim_left Afinal) at h0, cases h0, exact h0, cases (and.elim_left $ and.elim_right $ h0),
            constructor,
          },
          constructor,
        },
        cases q11, cases h0 with f _, cases f,
        cases h0 with f _, cases f,
      }
    },
    cases ih with ih ih,
    {
      simp,
      cases ih with eq ih, cases ih with v ih, cases ih with r ih,
      rw eq at h0, cases q00,
      repeat {cases h0 with f _, cases f,},
    },
    cases ih with ih ih,
    {
      cases ih with q0' ih, cases ih with eq ih,
      cases ih with finalq0' ih, cases ih with v ih,
      cases ih with r ih, cases ih with wvr ih,
      cases ih with ALang starLang, simp,
      rw eq at *,
      right, right,
      cases q00,
      {
        existsi q00, simp,
        existsi [[x], v ++ r],
        rw wvr, constructor, refl,
        cases q11,
        {
          existsi q11,
          injection eq with eq,
          constructor, rw eq, exact finalq0',
          constructor,
          {
            fconstructor,
            exact q11, cases h0, rw eq, exact h0, cases (and.elim_left $ and.elim_right $ h0),
            cases ALang, constructor,
          },
          constructor, exact ALang, exact starLang,
        },
        cases eq,
      },
      cases h0 with f _, cases f,
    },
    {
      cases ih with q0' ih, cases ih with eq ih,
      cases ih with v ih, cases ih with r ih,
      cases ih with wvr ih, cases ih with q1' ih,
      cases ih with finalq1' ih, cases ih with q0'vq1' starLang,
      simp, right, right,
      cases q00,
      {
        existsi q00, simp,
        existsi [(x :: v), r], rw wvr, constructor, refl,
        existsi q1', constructor, exact finalq1',
        constructor,
        {
          cases q11,
          {
            fconstructor,
            exact q11, cases h0, exact h0, cases (and.elim_left $ and.elim_right $ h0),
            injection eq with eq, rw eq, exact q0'vq1',
          },
          cases eq,
        },
        exact starLang,
      },
      cases q11, 
      repeat {cases h0 with f _, cases f,},
    }
  },
  case ε_nfa_δ_star.epsilon : q00 q11 q22 w h0 h1 ih
  {
    have ih := ih Afinal,
    cases ih with ih ih,
    {
      cases ih with wnil ih,
      cases ih with tofinal ih,
      {
        left, constructor, exact wnil,
        rw tofinal at *, right,
        cases q00,
        {
          right,
          existsi q00, simp,
          cases h0 with _ h0, exact (and.elim_left h0),
        },
        {
          left,
          cases h0 with _ h0, rw (and.elim_left h0),
        }
      },
      cases ih with fromstart Afinal,
      {
        left, constructor, exact wnil,
        rw fromstart at *,
        cases q00,
        {
          cases h0 with _ h0, right, right,
          existsi q00, constructor, refl, exact (and.elim_left h0),
        },
        {
          cases h0 with _ h0, cases h0 with _ f,
          cases f,
        },
      },
      {
        cases Afinal with q0' Afinal, cases Afinal with eq finalq0',
        rw eq at *, cases q00,
        {
          right, right, 
          cases h0,
          {
            right,
            existsi q00, constructor, refl,
            existsi [[], []], constructor, exact wnil,
            existsi q0', constructor, exact finalq0',
            constructor,
            {
              fconstructor,
              exact q0', exact h0, constructor,
            },
            constructor,
          },
          {
            left,
            existsi q00, constructor, refl,
            constructor, exact (and.elim_left h0),
            existsi [[], []], constructor, exact wnil,
            constructor,
            {
              existsi [q0', q0'], constructor, exact (and.elim_right $ and.elim_right $ h0),
              constructor, constructor, exact finalq0',
            },
            constructor,
          }
        },
        {
          cases h0 with _ h0,
          left, constructor, exact wnil,
          right, left, apply congr_arg, exact (and.elim_right h0),
        }
      },
    },
    cases ih with ih ih,
    {
      cases ih with eq ih, cases ih with v ih,
      cases ih with r ih, cases ih with wvr ih,
      cases ih with ALang starLang,
      right,
      cases q00,
      {
        right,
        cases q11,
        {
          cases eq,
        },
        {
          rw eq at h0, cases h0 with _ h0,
          cases (and.elim_right h0),
        }
      },
      {
        cases q11,
        {
          cases eq,
        },
        {
          cases h0 with _ h0, cases h0 with q00eq0 q11eq1,
          left, constructor, apply congr_arg, exact q00eq0,
          existsi [v, r], constructor, exact wvr,
          constructor, exact ALang, exact starLang,
        }
      }
    },
    cases ih with ih ih,
    {
      cases ih with q0' ih, cases ih with eq ih,
      cases ih with finalq0' ih, cases ih with v ih,
      cases ih with r ih, cases ih with wvr ih,
      cases ih with ALang starLang,
      right,
      cases q00,
      {
        rw eq at h0, right,
        cases h0,
        {
          right,
          existsi q00, simp,
          existsi [[], v ++ r], constructor, exact wvr,
          existsi q0', constructor, exact finalq0',
          constructor,
          {
            fconstructor, exact q0',
            exact h0, constructor,
          },
          constructor, exact ALang, exact starLang,
        },
        {
          left,
          cases h0 with finalq00 h0, cases h0 with _ initsq0',
          existsi q00, simp, constructor, exact finalq00,
          existsi [v, r], constructor, exact wvr,
          constructor, exact ALang, exact starLang,
        }
      },
      {
        rw eq at h0, cases h0 with _ h0,
        cases h0 with initsq0' q00eq0,
        left, constructor, apply congr_arg, exact q00eq0,
        existsi [v, r], constructor, exact wvr,
        constructor, exact ALang, exact starLang,
      }
    },
    {
      cases ih with q0' ih, cases ih with eq ih,
      cases ih with v ih, cases ih with r ih,
      cases ih with wvr ih, cases ih with q1' ih,
      cases ih with finalq1' ih, cases ih with q0'vq1' starLang,
      right, rw eq at h0,
      cases q00,
      {
        right,
        cases h0,
        {
          right, existsi q00,
          simp, existsi [v, r],
          constructor, exact wvr,
          existsi q1', constructor, exact finalq1',
          constructor,
          {
            fconstructor,
            exact q0', exact h0, exact q0'vq1',
          },
          exact starLang,
        },
        {
          left, existsi q00,
          simp, constructor, exact (and.elim_left h0),
          existsi [v, r], constructor, exact wvr,
          constructor,
          {
            existsi [q0', q1'],
            constructor, exact (and.elim_right $ and.elim_right $ h0),
            constructor, exact q0'vq1', exact finalq1',
          },
          exact starLang,
        }
      },
      {
        cases h0 with _ h0, cases h0 with initq0' q00eq0,
        left, constructor, apply congr_arg, exact q00eq0,
        existsi [v, r], constructor, exact wvr,
        constructor,
        {
          existsi [q0', q1'], constructor, exact initq0',
          constructor, exact q0'vq1', exact finalq1',
        },
        exact starLang,
      }
    }
  }
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
    cases h with init h, cases h with trans final,
    have g := star_lem A q0 q1 w (and.intro trans final),
    cases g,
    {
      rw (and.elim_left g), constructor,
    },
    cases g,
    {
      cases g with _ g, cases g with v g,
      cases g with r g, cases g with wvr g,
      cases g with ALang starLang, rw wvr,
      constructor, exact ALang, exact starLang,
    },
    cases g,
    {
      cases g with _ g, cases g with _ g,
      cases g with _ g, cases g with v g,
      cases g with r g, cases g with wvr g,
      cases g with ALang starLang, rw wvr,
      constructor, exact ALang, exact starLang,
    },
    {
      cases g with q0' g, cases g with eq g,
      cases init, cases eq,
    }
  },
  {
    assume h,
    dsimp [ε_nfa_lang],
    induction h,
    sorry,
    sorry,
  }
end
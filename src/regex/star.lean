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
    Q := A.Q ⊕ fin 1,
    finQ := @sum.fintype A.Q (fin 1) A.finQ (fin.fintype 1),
    decQ := @sum.decidable_eq A.Q A.decQ (fin 1) (fin.decidable_eq 1),
    inits := λ q, q = sum.inr 0,
    decI := begin
      assume a,
      cases a with q z,
      have f : ¬(λ (q : A.Q ⊕ fin 1), q = sum.inr 0) (sum.inl q),
      {
        assume h, cases h,
      },
      exact is_false f,
      have t : (λ (q : A.Q ⊕ fin 1), q = sum.inr 0) (sum.inr z),
      {
        finish,
      },
      exact is_true t,
    end,
    final := λ q, q = sum.inr 0,
    decF := begin
      assume a,
      cases a with q z,
      have f : ¬(λ (q : A.Q ⊕ fin 1), q = sum.inr 0) (sum.inl q),
      {
        assume h, cases h,
      },
      exact is_false f,
      have t : (λ (q : A.Q ⊕ fin 1), q = sum.inr 0) (sum.inr z),
      {
        finish,
      },
      exact is_true t,
    end, 
    δ := λ a x b, match a, x, b with
          | (sum.inl a), x, (sum.inl b) := A.δ a x b
          | (sum.inr a), x, (sum.inl b) := x = none ∧ A.inits b
          | (sum.inl a), x, (sum.inr b) := x = none ∧ A.final a
          | (sum.inr a), x, (sum.inr b) := false
        end,
    decD := begin
      assume a,
      cases a with ax b, cases ax with a x,
      cases a; cases b; dsimp [sigma.uncurry],
      exact A.decD ⟨⟨a, x⟩, b⟩,
      {
        letI dF := A.decF,
        letI decQ := @sum.decidable_eq A.Q A.decQ (fin 1) (fin.decidable_eq 1),
        unfold_aux,
        apply_instance,
      },
      {
        letI dI := A.decI,
        letI decQ := @sum.decidable_eq A.Q A.decQ (fin 1) (fin.decidable_eq 1),
        unfold_aux,
        apply_instance,
      },
      exact is_false id,
    end
  }

def state_lang (A : ε_nfa Sigma) : A.Q → lang Sigma :=
  λ q w, ∃ q' : A.Q, ε_nfa_δ_star A q w q' ∧ A.final q'

def lang1 (A : ε_nfa Sigma) : lang Sigma :=
  λ r , ∃ q : A.Q, A.inits q ∧ state_lang A q r

lemma star_lem1 : ∀ A : ε_nfa Sigma, ∀ q0 q1 : (star_ε_nfa A).Q, ∀ w : word Sigma,
  ε_nfa_δ_star (star_ε_nfa A) q0 w q1 ∧ (star_ε_nfa A).final q1 → 
  ∃ v r : word Sigma,
    w = v ++ r
    ∧ star_lang (ε_nfa_lang A) r
    ∧ ((∃ q0' : A.Q, (q0 = sum.inl q0' ∨ A.inits q0' ∧ q0 = q1) 
        ∧ ((∃ q1' : A.Q, ε_nfa_δ_star A q0' v q1' ∧ A.final q1')))
      ∨ (q0 = q1 ∧ v = [])) :=
begin
  assume A q0 q1 w h,
  cases h with h Afinal,
  induction h,
  case ε_nfa_δ_star.empty : q
  {
    existsi [[], []],
    simp, constructor,
  },
  case ε_nfa_δ_star.step : q00 q11 q22 x w h0 h1 ih
  {
    have ih := ih Afinal,
    cases ih with v ih, cases ih with r ih,
    cases ih with wvr ih, cases ih with starLang ih,
    existsi [(x :: v), r],
    constructor, exact congr_arg (list.cons x) wvr,
    constructor, exact starLang,
    left,
    cases ih with extend empty,
    {
      cases extend with q0' ih,
      cases ih with ih0 ih1,
      cases q00,
      {
        existsi q00, simp,
        cases ih0,
        {
          rw ih0 at *,
          cases ih1 with q1' ih, 
          existsi q1',
          constructor,
          {
            fconstructor,
            exact q0', exact h0, exact (and.elim_left ih),
          },
          exact (and.elim_right ih),
        },
        {
          cases Afinal,
          cases q11, cases (and.elim_right ih0),
          cases h0 with f _, cases f,
        },
      },
      {
        cases q11, cases h0 with f _, cases f,
        cases h0,
      },
    },
    {
      cases q00,
      {
        existsi [q00], constructor, left, refl,
        rw← (and.elim_left empty) at Afinal,
        cases Afinal,
        cases h0 with f _, cases f,
      },
      {
        cases q11, cases h0 with f _, cases f,
        cases h0,
      }
    }
  },
  case ε_nfa_δ_star.epsilon : q00 q11 q22 w h0 h1 ih
  {
    have ih := ih Afinal,
    cases ih with v ih, cases ih with r ih,
    cases ih with wvr ih, cases ih with starLang ih,
    existsi [v, r],
    constructor, exact wvr,
    constructor, exact starLang,
    cases q00,
    {
      cases q11,
      {
        cases ih with ih ih,
        {
          cases ih with q0' ih,
          cases ih with eq ih,
          cases eq,
          {
            injection eq with eq,
            cases ih with q1' ih,
            left,
            existsi q00, constructor, left, refl,
            existsi q1',
            constructor,
            {
              fconstructor,
              exact q11,
              exact h0,
              rw eq,
              exact (and.elim_left ih),
            },
            exact (and.elim_right ih),
          },
          cases Afinal, cases (and.elim_right eq),
        },
        {
          cases Afinal,
          cases (and.elim_left ih),
        }
      },
      {
        cases h0 with _ finalq00,
        cases ih with ih ih,
        {
          left,
          cases ih with q0' ih,
          simp at ih,
          cases ih with ih0 ih1,
          cases ih0 with initq0' q11r,
          cases ih1 with q1' ih1, cases ih1 with Astarv afinalq1',
          existsi q00, simp,
          sorry, 
        },
        {
          left,
          existsi q00,
          constructor, simp,
          existsi q00,
          constructor, rw (and.elim_right ih), constructor,
          exact finalq00, 
        }
      }
    },
    {
      cases q11,
      {
        dsimp [star_ε_nfa] at h0, cases h0 with _ initq11,
        cases Afinal,
        cases ih with extend empty,
        {
          cases extend with q11' extend,
          cases extend with eq Astarv,
          cases eq,
          {
            injection eq with eq,
            left, existsi q11,
            constructor,
            {
              right,
              constructor, exact initq11,
              apply congr_arg, exact fin.eq_zero q00,
            },
            {
              rw← eq at Astarv,
              exact Astarv,
            }
          },
          cases (and.elim_right eq),
        },
        {
          cases (and.elim_left empty),
        }
      },
      cases h0, 
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
    cases h with init h, cases h with star final,
    cases init, cases final,
    have g := star_lem1 A w q0 q1 (and.intro star final),
    cases g with v g, cases g with r g,
    cases g with wvr g, cases g with starLang g,
    cases g,
    {
      cases g with q2 g, cases g with q0q2 finalq2,
      rw wvr, fconstructor,
      {
        fconstructor, exact q0, existsi q2,
        constructor, exact init,
        constructor, exact q0q2, exact finalq2,
      },
      exact starLang,
    },
    {
      rw wvr, rw (and.elim_left $ and.elim_right $ g),
      simp, exact starLang,
    },
  },
  {
    assume h,
    dsimp [ε_nfa_lang],
    induction h,
    sorry,
    sorry,
  }
end
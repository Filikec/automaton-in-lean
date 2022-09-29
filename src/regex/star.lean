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
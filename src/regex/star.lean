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

lemma star_lem1 : ∀ A : ε_nfa Sigma, ∀ w : word Sigma, ∀ q0 q1 : (star_ε_nfa A).Q,
  ε_nfa_δ_star (star_ε_nfa A) q0 w q1 ∧ (star_ε_nfa A).final q1 →
    ∃ v r : word Sigma, 
      w = v ++ r 
      ∧ star_lang (ε_nfa_lang A) r
      ∧ ((∃ q2 : (star_ε_nfa A).Q, ε_nfa_δ_star A q0 v q2 ∧ A.final q2) 
      ∨ (A.inits q0 ∧ v = [] ∧ q0 = q1)) := 
begin
  assume A w q0 q1 h,
  cases h with Astar Afinal,
  induction Astar,
  case ε_nfa_δ_star.empty : q
  {
    existsi [[], []], simp,
    constructor, constructor,
    cases Afinal,
    left, existsi q, constructor, constructor, exact Afinal,
    right, exact Afinal,
  },
  case ε_nfa_δ_star.step : q00 q11 q22 x w h0 h1 ih
  {
    sorry,
  },
  case ε_nfa_δ_star.epsilon : q00 q11 q22 w h0 h1 ih
  {
    sorry,
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
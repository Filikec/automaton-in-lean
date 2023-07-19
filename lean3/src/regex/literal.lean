import data.fin.basic
import data.fintype.basic
import data.list
import ..automata_typeclass

variables {Sigma : Type} [decidable_eq Sigma]

def lit_lang (x : Sigma) : lang Sigma
:= λ w, w = x :: []

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

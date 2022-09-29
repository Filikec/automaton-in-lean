import data.fin.basic
import data.fintype.basic
import data.list
import ..automata_typeclass

variables {Sigma : Type} [decidable_eq Sigma]

def epsilon_lang : lang Sigma
:= λ w, w = []

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
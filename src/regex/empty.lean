import data.fin.basic
import data.fintype.basic
import data.list
import ..automata_typeclass

variables {Sigma : Type} [decidable_eq Sigma]

def empty_lang : lang Sigma
:= λ _, false

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
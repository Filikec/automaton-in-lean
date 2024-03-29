import data.fintype.basic
import tactic.derive_fintype

section basics
variable Sigma : Type

@[reducible]
def word : Type := list Sigma

@[reducible]
def lang : Type := word Sigma → Prop

end basics 


section dfa
variable {Sigma : Type}

structure dfa(Sigma : Type*) :=
  (Q : Type*)
  [finQ : fintype Q]
  [decQ : decidable_eq Q]
  (init : Q)
  (final : Q → Prop)
  [decF : decidable_pred final] 
  (δ : Q → Sigma → Q)

open dfa

def dfa_δ_star (A : dfa Sigma) : A.Q → word Sigma → A.Q
| q [] := q
| q (x :: w) := dfa_δ_star (A.δ q x) w

def dfa_lang (A : dfa Sigma) : lang Sigma
:= λ w , A.final (dfa_δ_star A A.init w)

end dfa


section nfa
variables {Sigma : Type}

structure nfa(Sigma : Type*) := 
  (Q : Type*)
  [finQ : fintype Q]
  [decQ : decidable_eq Q]
  (inits : Q → Prop)
  [decI : decidable_pred inits]
  (final : Q → Prop)
  [decF : decidable_pred final]
  (δ : Q → Sigma → Q → Prop)
  [decD : decidable_pred (sigma.uncurry (sigma.uncurry δ))]

open nfa

def nfa_δ_star : Π A : nfa Sigma , A.Q → word Sigma → A.Q → Prop 
| A q0 [] q1 := q0 = q1
| A q0 (x :: w) q1 := ∃ q2 : A.Q, A.δ q0 x q2 ∧ nfa_δ_star A q2 w q1

def nfa_lang (A : nfa Sigma) : lang Sigma
:= λ w , ∃ q0 q1 : A.Q, A.inits q0 ∧ nfa_δ_star A q0 w q1 ∧ A.final q1

def empty_nfa {Sigma : Type*} : nfa Sigma :=
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

def epsilon_nfa {Sigma : Type*} : nfa Sigma :=
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

def single_nfa {Sigma : Type*} [decidable_eq Sigma] (lit : Sigma) : nfa Sigma :=
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

end nfa


section ε_nfa
variables {Sigma : Type} [decidable_eq Sigma]

structure ε_nfa(Sigma : Type) :=
  (Q : Type*)
  [finQ : fintype Q]
  [decQ : decidable_eq Q]
  (inits : Q → Prop)
  [decI : decidable_pred inits]
  (final : Q → Prop)
  [decF : decidable_pred final]
  (δ : Q → option Sigma → Q → Prop)
  [decD : decidable_pred (sigma.uncurry (sigma.uncurry δ))]

open ε_nfa

inductive ε_closure{A : ε_nfa Sigma} : (A.Q → Prop) → A.Q → Prop
| base : ∀ x : A.Q → Prop, ∀ q : A.Q, x q → ε_closure x q
| step : ∀ x : A.Q → Prop, ∀ q q' : A.Q, ε_closure x q → A.δ q none q' → ε_closure x q'

/-
def ε_nfa_δ_star : Π A : ε_nfa Sigma , A.Q → word Sigma → A.Q → Prop 
| A q0 [] q1 := ε_closure (λ q, q = q0) q1
| A q0 (x :: w) q1 := ∃ q2 : A.Q, (A.δ q0 (some x) q2 ∨ A.δ q0 none q2) ∧  ε_nfa_δ_star A q2 w q1
-/

inductive ε_nfa_δ_star (A : ε_nfa Sigma) : A.Q → word Sigma → A.Q → Prop 
| empty : ∀ q : A.Q , ε_nfa_δ_star q [] q
| step : ∀ q0 q1 q2 : A.Q, ∀ x : Sigma, ∀ w : word Sigma,
            A.δ q0 (some x) q1 → ε_nfa_δ_star q1 w q2 → ε_nfa_δ_star q0 (x :: w) q2 
| epsilon : ∀ q0 q1 q2 : A.Q, ∀ w : word Sigma, 
            A.δ q0 none q1 → ε_nfa_δ_star q1 w q2 → ε_nfa_δ_star q0 w q2 

def ε_nfa_lang (A : ε_nfa Sigma) : lang Sigma
:= λ w , ∃ q0 q1 : A.Q, A.inits q0 ∧ ε_nfa_δ_star A q0 w q1 ∧ A.final q1


theorem inversion : ∀ A : ε_nfa Sigma, ∀ q q' : A.Q, ∀ w : word Sigma,
        ε_nfa_δ_star A q w q' →
        (w = [] ∧ q' = q)
        ∨ (∃ x : Sigma, ∃ w' : word Sigma, ∃ q'' : A.Q , w = x :: w' ∧ A.δ q (some x) q'' ∧ ε_nfa_δ_star A q'' w' q')
        ∨ (∃ q'' : A.Q , A.δ q none q'' ∧ ε_nfa_δ_star A q'' w q') :=
begin
  assume A q q' w,
  assume h,
  cases h,
  left,
  constructor,
  refl,
  refl,
  right, left,
  existsi h_x,
  existsi h_w,
  existsi h_q1,
  constructor,
  refl,
  constructor,
  exact h_ᾰ,
  exact h_ᾰ_1,
  right, right,
  existsi h_q1,
  constructor,
  exact h_ᾰ,
  exact h_ᾰ_1,
end

end ε_nfa


section dfa2nfa 
variables {Sigma : Type}

def dfa2nfa(A : dfa Sigma) : nfa Sigma :=
  {
    Q := A.Q,
    finQ := A.finQ,
    decQ := A.decQ,
    inits := λ q : A.Q, q = A.init,
    decI := λ q, A.decQ q A.init,
    final := A.final,
    decF := A.decF,
    δ := λ q0 x q1 , q1 = A.δ q0 x,
    decD := λ q , A.decQ q.snd (A.δ q.fst.fst q.fst.snd),
  }

lemma nfaδ2dfaδ : ∀ A : dfa Sigma, ∀ w : word Sigma,
  ∀ q0 q1 : A.Q, dfa_δ_star A q0 w = q1 ↔ nfa_δ_star (dfa2nfa A) q0 w q1 :=
begin
  assume A w,
  induction w,
  {
    assume q0 q1,
    constructor,
    dsimp [dfa_δ_star, nfa_δ_star],
    assume h,
    exact h,
    dsimp [dfa_δ_star, nfa_δ_star],
    assume h,
    exact h,
  },
  {
    assume q0 q1,
    constructor,
    {
      assume h,
      dsimp [nfa_δ_star],
      existsi A.δ q0 w_hd,
      constructor,
      dsimp [dfa2nfa],
      reflexivity,
      apply (iff.mp (w_ih (A.δ q0 w_hd) q1)),
      exact h,
    },
    {
      dsimp [dfa_δ_star, nfa_δ_star],
      assume g,
      apply (iff.mpr (w_ih (A.δ q0 w_hd) q1)),
      cases g with q00 gg,
      have eq: A.δ q0 w_hd = q00,
      dsimp [dfa2nfa] at gg,
      exact (eq.symm (and.elim_left gg)),
      rewrite eq,
      exact (and.elim_right gg),
    }
  }
end

lemma emb11 : ∀ A : dfa Sigma, ∀ w : word Sigma, 
    dfa_lang A w → nfa_lang (dfa2nfa A) w :=
begin
  assume A w,
  dsimp [dfa_lang, nfa_lang],
  induction w,
  {
    dsimp [dfa_δ_star],
    assume h,
    existsi A.init,
    existsi A.init,
    constructor,
    dsimp [dfa2nfa],
    reflexivity,
    constructor,
    dsimp [nfa_δ_star],
    reflexivity,
    dsimp [dfa2nfa],
    exact h,
  },
  {
    assume h,
    existsi A.init,
    existsi (dfa_δ_star A A.init (w_hd :: w_tl)),
    constructor,
    dsimp [dfa2nfa],
    reflexivity,
    constructor,
    dsimp [nfa_δ_star],
    existsi A.δ A.init w_hd,
    constructor,
    dsimp [dfa2nfa],
    reflexivity,
    dsimp [dfa_δ_star],
    apply iff.mp (nfaδ2dfaδ A w_tl (A.δ A.init w_hd) (dfa_δ_star A (A.δ A.init w_hd) w_tl)),
    reflexivity,
    dsimp [dfa2nfa],
    exact h,
  }
end

lemma emb12 : ∀ A : dfa Sigma, ∀ w : word Sigma, 
    nfa_lang (dfa2nfa A) w → dfa_lang A w :=
begin
  assume A w,
  dsimp [nfa_lang, dfa_lang],
  assume h,
  induction w,
  {
    dsimp [dfa_δ_star] at *,
    cases h with q0 h2,
    cases h2 with q1 h3,
    dsimp [nfa_δ_star, dfa2nfa] at h3,
    rewrite← (and.elim_left h3),
    rewrite (and.elim_left (and.elim_right h3)),
    exact (and.elim_right (and.elim_right h3)),
  },
  {
    dsimp [dfa_δ_star] at *,
    cases h with q0 h2,
    cases h2 with q1 h3,
    have eq: q0 = A.init,
    dsimp [dfa2nfa] at h3,
    exact and.elim_left h3,
    have g: dfa_δ_star A (A.δ A.init w_hd) w_tl = q1,
    rewrite← eq,
    change dfa_δ_star A q0 (w_hd :: w_tl) = q1,
    apply (iff.mpr (nfaδ2dfaδ A (w_hd :: w_tl) q0 q1)),  
    exact and.elim_left (and.elim_right h3),
    rewrite g,
    exact and.elim_right (and.elim_right h3),
  }
end

lemma emb1 : ∀ A : dfa Sigma, ∀ w : word Sigma, 
    dfa_lang A w ↔ nfa_lang (dfa2nfa A) w :=
begin
  assume A w,
  constructor,
  exact (emb11 A w),
  exact (emb12 A w),
end

end dfa2nfa


section nfa2dfa
variables {Sigma : Type}

@[reducible]
def decPow (A : Type*) := Σ (p : A → Prop), decidable_pred p

-- https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/fintype.20for.20functions/near/291226330
def equiv.sigma_decidable_pred {α : Type*} : (Σ (p : α → Prop), decidable_pred p) ≃ (α → bool) :=
  {
    to_fun := λ A i, @to_bool (A.1 i) (A.2 i),
    inv_fun := λ p, ⟨λ a, p a, by apply_instance⟩,
    left_inv := λ p, sigma.ext (by simp) $ subsingleton.helim (by simp) _ _,
    right_inv := λ p, funext $ λ i, bool.to_bool_coe _
  }

instance finpow {A : Type*} (fin : fintype A) (dec : decidable_eq A) : fintype (decPow A) :=
fintype.of_equiv (A → bool) $ equiv.symm equiv.sigma_decidable_pred

instance decpow {A : Type*} (fin : fintype A) (dec : decidable_eq A) : decidable_eq (decPow A) :=
equiv.decidable_eq equiv.sigma_decidable_pred

def nfa2dfa (A : nfa Sigma) : dfa Sigma :=
  {
    Q := decPow A.Q,
    finQ := finpow A.finQ A.decQ,
    decQ := decpow A.finQ A.decQ,
    init := sigma.mk (A.inits) A.decI,
    final := λ p, ∃ q, p.1 q ∧ A.final q,
    decF := 
      begin
        assume p,
        casesI p,
        letI decF: decidable_pred A.final := A.decF,
        letI finQ: fintype A.Q := A.finQ,
        simp at *,
        apply fintype.decidable_exists_fintype,
      end,
    δ := λ p x, ⟨(λ q1, ∃ q0 : A.Q, p.1 q0 ∧ A.δ q0 x q1), 
                  λ q1, begin
                    casesI p,
                    letI finQ: fintype A.Q := A.finQ,
                    simp at *,
                    letI decD: decidable_pred (λ q0, p_fst q0 ∧ A.δ q0 x q1),
                    {
                      assume q0,
                      simp at *,
                      casesI p_snd q0,
                      have f: ¬ (p_fst q0 ∧ A.δ q0 x q1),
                      {
                        assume h2,
                        apply h,
                        exact (and.elim_left h2),
                      },
                      exact is_false f,
                      casesI A.decD ⟨⟨q0, x⟩, q1⟩ with no yes,
                      have f: ¬ (p_fst q0 ∧ A.δ q0 x q1),
                      {
                        assume h2,
                        apply no,
                        dsimp [sigma.uncurry],
                        exact (and.elim_right h2),
                      },
                      exact is_false f,
                      dsimp [sigma.uncurry] at yes,
                      exact is_true (and.intro h yes),
                    },
                    apply fintype.decidable_exists_fintype,
                  end⟩,
  }

lemma dfaδ2nfaδ : ∀ A : nfa Sigma, ∀ w : word Sigma, 
  ∀ q1 : A.Q, ∀ p : (nfa2dfa A).Q,
  (∃ q0 : A.Q, p.1 q0 ∧ nfa_δ_star A q0 w q1) ↔ (dfa_δ_star (nfa2dfa A) p w).1 q1
  :=
begin
  assume A w,
  induction w,
  {
    assume q1 p,
    dsimp [nfa_δ_star, dfa_δ_star],
    constructor,
    {
      assume h,
      cases h with q0 h2,
      rewrite← (and.elim_right h2),
      exact (and.elim_left h2),
    },
    {
      assume h,
      existsi q1,
      exact (and.intro h rfl),
    },
  },
  {
    assume q1 p,
    dsimp [nfa_δ_star, dfa_δ_star],
    constructor,
    {
      assume h,
      cases h with q0 h2,
      cases (and.elim_right h2) with q2 h3,
      have g: ((nfa2dfa A).δ p w_hd).1 q2,
      {
        dsimp [nfa2dfa],
        existsi q0,
        exact (and.intro (and.elim_left h2) (and.elim_left h3)),
      },
      apply (iff.mp (w_ih q1 ((nfa2dfa A).δ p w_hd))),
      existsi q2,
      exact (and.intro g (and.elim_right h3)),
    },
    { 
      assume h,
      cases iff.mpr (w_ih q1 ((nfa2dfa A).δ p w_hd)) h with q2 h2,
      dsimp [nfa2dfa] at h2,
      cases (and.elim_left h2) with q0 h3,
      existsi q0,
      constructor,
      exact (and.elim_left h3),
      existsi q2,
      exact (and.intro (and.elim_right h3) (and.elim_right h2)),
    },
  }
end

lemma emb21 : ∀ A : nfa Sigma, ∀ w : word Sigma,
  nfa_lang A w → dfa_lang (nfa2dfa A) w :=
begin
  assume A w,
  dsimp [nfa_lang, dfa_lang],
  induction w,
  {
    dsimp [nfa_δ_star, dfa_δ_star],
    assume h,
    dsimp [nfa2dfa],
    cases h with q0 h2,
    cases h2 with q1 h3,
    existsi q0,
    constructor,
    exact (and.elim_left h3),
    rewrite (and.elim_left (and.elim_right h3)),
    exact (and.elim_right (and.elim_right h3)),
  },
  {
    dsimp [nfa_δ_star, dfa_δ_star],
    assume h,
    cases h with q0 h2,
    cases h2 with q1 h3,
    have g: (dfa_δ_star (nfa2dfa A) ((nfa2dfa A).δ (nfa2dfa A).init w_hd) w_tl).1 q1,
    {
      apply iff.mp (dfaδ2nfaδ A w_tl q1 ((nfa2dfa A).δ (nfa2dfa A).init w_hd)),
      cases (and.elim_left (and.elim_right h3)) with q2 h4,
      existsi q2,
      dsimp [nfa2dfa],
      constructor,
      existsi q0,
      exact (and.intro (and.elim_left h3) (and.elim_left h4)),
      exact (and.elim_right h4),
    },
    existsi q1,
    exact (and.intro g (and.elim_right (and.elim_right h3))),
  }
end

lemma emb22 : ∀ A : nfa Sigma, ∀ w : word Sigma,
  dfa_lang (nfa2dfa A) w → nfa_lang A w :=
begin
  assume A w,
  dsimp [nfa_lang, dfa_lang],
  induction w,
  {
    dsimp [nfa_δ_star, dfa_δ_star, nfa2dfa],
    assume h,
    cases h with q0 h2,
    existsi q0,
    existsi q0,
    simp,
    exact h2,
  },
  {
    assume h,
    cases h with q1 h2,
    have g: ∃ q0 : A.Q, (nfa2dfa A).init.1 q0 ∧ nfa_δ_star A q0 (w_hd :: w_tl) q1,
    {
      apply iff.mpr (dfaδ2nfaδ A (w_hd :: w_tl) q1 (nfa2dfa A).init),
      exact (and.elim_left h2),
    },
    cases g with q0 gg,
    existsi q0,
    existsi q1,
    constructor,
    exact (and.elim_left gg),
    exact (and.intro (and.elim_right gg) (and.elim_right h2)),
  }
end

lemma emb2 : ∀ A : nfa Sigma, ∀ w : word Sigma,
  nfa_lang A w ↔ dfa_lang (nfa2dfa A) w :=
begin
  assume A w,
  constructor,
  exact emb21 A w,
  exact emb22 A w,
end

end nfa2dfa


section nfa2ε_nfa

variables {Sigma : Type} [decidable_eq Sigma]

def nfa2ε_nfa(A : nfa Sigma) : ε_nfa Sigma :=
  {
    Q := A.Q,
    finQ := A.finQ,
    decQ := A.decQ,
    inits := A.inits,
    decI := A.decI,
    final := A.final,
    decF := A.decF,
    δ := λ q0 x q1, x.cases_on' false (λ x, A.δ q0 x q1),
    decD := λ q, begin
      dsimp[sigma.uncurry],
      cases q with q0x q1,
      cases q0x with q0 x,
      cases x with x empty,
      {
        dsimp[option.cases_on'],
        letI g:= A.decQ,
        apply_instance,
      },
      {
        dsimp[option.cases_on'],
        exact (A.decD ⟨⟨q0, x⟩, q1⟩),
      }
    end,
  }

lemma nfaδ2ε_nfaδ : ∀ A : nfa Sigma, ∀ w : word Sigma, 
  ∀ q0 q1 : A.Q,
  (nfa_δ_star A q0 w q1) ↔ ε_nfa_δ_star (nfa2ε_nfa A) q0 w q1
  :=
begin
  assume A w,
  induction w,
  {
    assume q0 q1,
    dsimp [nfa_δ_star],
    constructor,
    assume eq,
    rewrite eq,
    fconstructor,
    assume h,
    cases h,
    {
      refl,
    },
    {
      dsimp [nfa2ε_nfa] at *,
      cases h_ᾰ,
    },
  },
  {
    assume q0 q1,
    dsimp [nfa_δ_star],
    constructor,
    {
      assume h,
      cases h with q2 h2,
      dsimp [nfa2ε_nfa],
      cases h2,
      fconstructor,
      exact q2,
      exact h2_left,
      apply iff.mp (w_ih q2 q1),
      exact h2_right,
    },
    {
      assume h,
      cases h,
      {
        existsi h_q1,
        constructor,
        exact h_ᾰ,
        apply iff.mpr (w_ih h_q1 q1),
        exact h_ᾰ_1,
      },
      {
        dsimp [nfa2ε_nfa] at h_ᾰ,
        cases h_ᾰ,
      },
    },
  }
end

lemma emb3 : ∀ A : nfa Sigma, ∀ w : word Sigma,
  nfa_lang A w ↔ ε_nfa_lang (nfa2ε_nfa A) w :=
begin
  assume A w,
  dsimp [nfa_lang, ε_nfa_lang],
  constructor,
  { 
    assume h,
    cases h with q0 h2,
    cases h2 with q1 h3,
    existsi q0,
    existsi q1,
    constructor,
    exact (and.elim_left h3),
    constructor,
    {
      cases h3,
      apply iff.mp (nfaδ2ε_nfaδ A w q0 q1),
      exact and.elim_left h3_right,
    },
    exact (and.elim_right (and.elim_right h3)),
  },
  {
    assume h,
    cases h with q0 h2,
    cases h2 with q1 h3,
    cases h3 with h4 h5,
    cases h5 with h6 h7,
    existsi q0,
    existsi q1,
    constructor,
    exact h4,
    constructor,
    apply iff.mpr (nfaδ2ε_nfaδ A w q0 q1),
    exact h6,
    exact h7,
  }
end

end nfa2ε_nfa
section basics
variable Sigma : Type

def word : Type := list Sigma

def lang : Type := word Sigma → Prop

end basics 


section dfa
variable {Sigma : Type}

structure dfa(Sigma : Type)  : Type 1 :=
  (Q : Type)
  (init : Q)
  (final : Q → Prop)
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

structure nfa(Sigma : Type) : Type 1 := 
  (Q : Type)
  (inits : Q → Prop)
  (final : Q → Prop)
  (δ : Q → Sigma → Q → Prop)

open nfa

/--/
inductive nfa_δ_star (A : nfa Sigma) : A.Q → word Sigma → A.Q → Prop 
| empty : ∀ q : A.Q , nfa_δ_star q [] q
| step : ∀ q0 q1 q2 : A.Q, ∀ x : Sigma, ∀ w : word Sigma, 
            A.δ q0 x q1 → nfa_δ_star q1 w q2 → nfa_δ_star q1 (x :: w) q2 
-/

def nfa_δ_star : Π A : nfa Sigma , A.Q → word Sigma → A.Q → Prop 
| A q0 [] q1 := q0 = q1
| A q0 (x :: w) q1 := ∃ q2 : A.Q, A.δ q0 x q2 ∧ nfa_δ_star A q2 w q1

def nfa_lang (A : nfa Sigma) : lang Sigma
:= λ w , ∃ q0 q1 : A.Q, A.inits q0 ∧ nfa_δ_star A q0 w q1 ∧ A.final q1

end nfa


section dfa2nfa 
variables {Sigma : Type}

def dfa2nfa(A : dfa Sigma) : nfa Sigma :=
  {
    Q := A.Q,
    inits := λ q , q = A.init,
    final := A.final,
    δ := λ q0 x q1 , q1 = A.δ q0 x
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

def nfa2dfa(A : nfa Sigma) : dfa Sigma :=
  {
    Q := A.Q → Prop,
    init := A.inits,
    final := λ p , ∃ q : A.Q, p q ∧ A.final q,
    δ := λ p x q1 , ∃ q0 : A.Q, p q0 ∧ A.δ q0 x q1, 
  }

lemma dfaδ2nfaδ : ∀ A : nfa Sigma, ∀ w : word Sigma, 
  ∀ q1 : A.Q, ∀ p : (nfa2dfa A).Q,
  (∃ q0 : A.Q, p q0 ∧ nfa_δ_star A q0 w q1) ↔ dfa_δ_star (nfa2dfa A) p w q1
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
      have g: ((nfa2dfa A).δ p w_hd) q2,
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
    have g: dfa_δ_star (nfa2dfa A) ((nfa2dfa A).δ (nfa2dfa A).init w_hd) w_tl q1,
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
    have g: ∃ q0 : A.Q, (nfa2dfa A).init q0 ∧ nfa_δ_star A q0 (w_hd :: w_tl) q1,
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

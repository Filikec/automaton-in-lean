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
  {Q := A.Q,
   inits := λ q , q = A.init,
   final := A.final,
   δ := λ q0 x q1 , q1 = A.δ q0 x
  }

lemma emb1 : ∀ A : dfa Sigma, ∀ w : word Sigma, 
    dfa_lang A w ↔ nfa_lang (dfa2nfa A) w :=
begin
  assume A w,
  dsimp [dfa_lang,nfa_lang],
  induction w,
  {
    -- nil case
    dsimp [dfa_δ_star],
    constructor,
    {
      -- dfa to nfa 
      assume h,
      existsi A.init,
      existsi A.init,
      constructor,
      dsimp [dfa2nfa],
      reflexivity,
      dsimp [nfa_δ_star],
      constructor,
      reflexivity,
      dsimp [dfa2nfa],
      exact h,
    },
    {
      -- nfa to dfa
      dsimp [dfa2nfa,nfa_δ_star],
      assume h,
      cases h with q0 h_h,
      cases h_h with q1 h_h_h,
      cases h_h_h with initq0 eq,
      cases eq with q0q1 finalq1,
      rewrite<- initq0,
      rewrite q0q1,
      exact finalq1,
    },
  },
  {
    -- cons case
    dsimp [dfa_δ_star,nfa_δ_star],
    cases w_ih with d2n_ih n2d_ih,
    constructor,
    {
      -- dfa to nfa
      assume h,
      existsi A.init,
      existsi (dfa_δ_star A A.init w_tl),
      constructor,
      dsimp [dfa2nfa],
      reflexivity,
      constructor,
      existsi (A.δ A.init w_hd),
      constructor,
      dsimp [dfa2nfa],
      reflexivity,      
      sorry,
      dsimp [dfa2nfa],
      --
      sorry,
    },
    {
      -- nfa to dfa
      assume h,
      cases h with nfainit h2,
      cases h2 with q1 h3,
      cases h3 with h_nfainit h4,
      cases h4 with h5 h_q1final,
      cases h5 with q2 h6,
      cases h6 with init2q2 q22q1,
      sorry,
    }
  }
end

end dfa2nfa
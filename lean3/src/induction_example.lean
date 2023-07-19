import tactic
open nat

inductive le : ℕ → ℕ → Prop
| le0 {n : ℕ} : le 0 n
| les {m n : ℕ} : le m n → le (succ m) (succ n)

open le

inductive le' : ℕ → ℕ → Prop
| reflle' {n : ℕ} : le' n n
| le's {m n : ℕ} : le' m n → le' m (succ n)

open le'

lemma l1 : ∀ n : ℕ, le' zero n :=
begin 
  assume n,
  induction n,
  exact reflle',
  apply le's,
  exact n_ih,
end

lemma l2 : ∀ m n : ℕ, le' m n → le' (succ m) (succ n) :=
begin
  assume m n h,
  induction h,
  {
    exact reflle',
  },
  {
    apply le's,
    exact h_ih,
  }
end

lemma l3 : ∀ n : ℕ, le n n :=
begin
  assume n,
  induction n,
  exact le0,
  apply les,
  exact n_ih,
end

lemma l4 : ∀ m n : ℕ, le m n → le m (succ n) :=
begin
  assume m n h,
  induction h,
  {
    exact le0,
  },
  {
    apply les,
    exact h_ih,
  }
end

theorem equ {m n : ℕ} : le m n ↔ le' m n :=
begin
  constructor,
  {
    assume h,
    induction h,
    {
      exact l1 h,
    },
    {
      apply l2,
      exact h_ih,
    }
  },
  {
    assume h,
    induction h,
    {
      exact l3 h,
    },
    {
      apply l4,
      exact h_ih,
    }
  }
end

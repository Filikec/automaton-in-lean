import Mathlib.Init.Set

variable (Sigma : Type _)

@[reducible]
def word : Type _ := List Sigma

@[reducible]
def Lang : Type _ := Set (word Sigma)

def power {Sigma : _ } (l : word Sigma) : Nat → word Sigma
  | 0  => []
  | n+1  => l ++ power l n

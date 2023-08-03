import Mathlib.Init.Set

variable (Sigma : Type _)

@[reducible]
def word : Type _ := List Sigma

@[reducible]
def Lang : Type _ := Set (word Sigma)
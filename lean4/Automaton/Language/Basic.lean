import Mathlib.Init.Set

variable (Sigma : Type _)

@[reducible]
def word : Type := List Sigma

@[reducible]
def Lang : Type := Set (word Sigma)
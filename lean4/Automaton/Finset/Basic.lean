import Mathlib.Data.Finset.Basic


namespace Finset

theorem nonempty_inter_singleton_imp_in {α : Type _} [DecidableEq α] (e : α) (es : Finset α) : 
  Finset.Nonempty ({e} ∩ es) → e ∈ es := by
    intro ne
    have h₁ : e ∉ es → {e} ∩ es = ∅ := Finset.singleton_inter_of_not_mem
    have h₂ := Not.imp_symm h₁
    apply h₂
    apply (Iff.mp Finset.nonempty_iff_ne_empty)
    exact ne

end Finset
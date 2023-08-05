import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.FinEnum

namespace Finset

variable {α β : Type _}

theorem nonempty_inter_singleton_imp_in  [DecidableEq α] (e : α) (es : Finset α) : 
  Finset.Nonempty ({e} ∩ es) → e ∈ es := by
    intro ne
    have h₁ : e ∉ es → {e} ∩ es = ∅ := Finset.singleton_inter_of_not_mem
    have h₂ := Not.imp_symm h₁
    apply h₂
    apply (Iff.mp Finset.nonempty_iff_ne_empty)
    exact ne

def fin_of_subtype_to_subtype_of_subfin {qs : Finset α} (s : Finset { x // x ∈ qs }) : { x // x ⊆ Finset.attach qs } := by 
  exact ⟨s , fun x => by simp⟩ 

def subtype_of_subfin_to_fin_of_subtype {qs : Finset α}  (s : { x // x ⊆ Finset.attach qs }) : (Finset { x // x ∈ qs }) := by 
  exact s.1

def subtype_of_sset_subtype {α : Type _} {s ss : Finset α} (e : { x // x ∈ ss}) : ss ⊆ s → { x // x ∈ s} := by
  intro iss
  exact ⟨ e.1 , by simp; apply Finset.mem_of_subset iss; exact e.2⟩ 


def finenum_to_finset (α : Type _) [FinEnum α] : Finset α := ⟨ Multiset.ofList (FinEnum.toList α) , by apply FinEnum.nodup_toList⟩

end Finset
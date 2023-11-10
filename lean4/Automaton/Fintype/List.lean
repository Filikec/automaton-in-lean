import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Perm

variable {α : Type _} {fa : Finset α} [DecidableEq α] (n : Nat)

theorem perm_eq_len {l₁ l₂ : List β} : l₁ ~ l₂ → l₁.length = l₂.length := by
  intro p
  induction p with
  | nil => simp
  | cons e p eq => simp; exact eq
  | swap _ _ => simp
  | trans p₁ p₂ eq₁ eq₂ => rw [eq₁]; exact eq₂


lemma perm_of_finset_of_perms (l : List α) : ∀ p : l.permutations.toFinset, p ~ l := by
  intro p
  have := p.2
  simp at this
  exact this


def add_element_to_list (a : fa) (l : { x : List fa // List.length x = n }) : Finset {x : List fa // List.length x = n.succ} := by
  let perms := (a::l.1).permutations.toFinset
  have le : (a::l.1).length = n.succ := by simp
                                           exact l.2
  exact perms.attach.map ⟨fun p => ⟨p.1, by rw [←le]; apply perm_eq_len;  apply perm_of_finset_of_perms ⟩, by simp [Function.Injective]⟩


def add_element_to_fintype (a : fa) : Fintype {x : List fa // x.length = n} → Finset {x : List fa // x.length = n.succ} := by
  intro ft
  exact ft.elems.biUnion (fun l => add_element_to_list n a l)


theorem fintype_list_fintype_eq_n {n : Nat} : Fintype {x : List fa // x.length = n} := by
  induction n with
  | zero => exact ⟨ {⟨[] , by simp⟩}, by simp; intro l e; apply List.length_eq_zero.mp; exact e⟩
  | succ n s => let f : Finset { x : List fa // x.length = Nat.succ n} := Finset.biUnion (fa.attach) (fun a => add_element_to_fintype n a s)
                exact ⟨f , by intro x
                              simp
                              cases (Decidable.em (x.1 = [])) with
                              | inl h => have e₁ := List.length_eq_zero.mpr h
                                         have e₂ := x.2
                                         rw [e₁] at e₂
                                         contradiction
                              | inr h => have := List.exists_cons_of_ne_nil h
                                         apply Exists.elim this
                                         intro e ex
                                         apply Exists.elim ex
                                         intro l eq
                                         exists e
                                         exists e.2
                                         simp [add_element_to_fintype]
                                         exists l
                                         have lx := x.2
                                         rw [eq] at lx
                                         simp only [List.length] at lx
                                         rw [Nat.succ_eq_add_one] at lx
                                         have : List.length l = n :=  Nat.add_right_cancel lx
                                         exists this
                                         apply And.intro
                                         · apply s.2
                                         · simp [add_element_to_list]
                                           exists (e::l)
                                           simp
                                           apply Subtype.mk_eq_mk.mpr
                                           apply Eq.symm
                                           exact eq⟩


lemma le_sn_gt_n_eq_n (m : Nat) : (n : Nat) → m ≤ Nat.succ n → ¬(m ≤ n) → m = Nat.succ n := by
  induction m with
  | zero => intro n _ nle
            simp at nle
  | succ m h => intro n
                match n with
                | 0 =>  intro le _
                        apply congr_arg
                        have := Nat.le_of_succ_le_succ le
                        apply Nat.le_zero.mp
                        exact this
                | (Nat.succ n) => intro le nle
                                  apply congr_arg
                                  apply h
                                  · have := Nat.le_of_succ_le_succ le
                                    exact this
                                  · intro le
                                    apply nle
                                    apply Nat.succ_le_succ
                                    exact le


theorem fintype_list_fintype_le_n {n : Nat} : Fintype {x : List fa // x.length <= n} := by
  induction n with
  | zero => exact ⟨ {⟨ [], by simp⟩ }, by simp; intro l e; apply List.length_eq_zero.mp; exact e⟩
  | succ n s => have fe : Fintype { x : List fa // List.length x = Nat.succ n } := fintype_list_fintype_eq_n
                let sle : Finset { x : List fa // List.length x ≤ Nat.succ n } := s.elems.map ⟨fun e => ⟨ e.1, by apply Nat.le_succ_of_le; exact e.2  ⟩, by simp [Function.Injective]⟩
                let fle : Finset { x : List fa // List.length x ≤ Nat.succ n } := fe.elems.map ⟨fun e => ⟨ e.1, by apply Nat.le_of_eq; exact e.2  ⟩, by simp [Function.Injective]⟩
                exact ⟨ sle ∪ fle, by intro x
                                      simp
                                      cases (Decidable.em (x.1.length ≤ n)) with
                                      | inl g => apply Or.inl
                                                 exists x.1
                                                 · exists g
                                                   simp
                                                   apply s.2
                                      | inr g => have : List.length x.1 = (Nat.succ n) := le_sn_gt_n_eq_n (List.length x.1) n x.2 g
                                                 apply Or.inr
                                                 exists x.1
                                                 · exists this
                                                   simp
                                                   apply fe.2⟩

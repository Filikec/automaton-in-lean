import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Automaton.DFA.Basic
import Automaton.DFA.Minimization
import Automaton.DFA.PumpingLemma

/-!
  Concrete examples of DFA
-/

open DFA PumpingLemma

-- need to be able to synth FinEnum to print the DFA
def Q : Finset (Fin 2) := {0,1}
def σ : Finset (Fin 2) := {0,1}

def δ₁ : Q → σ → Q
  | ⟨0,_⟩ , ⟨0,_⟩ => ⟨0, by simp⟩
  | ⟨0,_⟩ , ⟨1,_⟩ => ⟨1, by simp⟩
  | ⟨1,_⟩ , ⟨0,_⟩ => ⟨0, by simp⟩
  | ⟨1,_⟩ , ⟨1,_⟩ => ⟨1, by simp⟩

-- accepts all words that end with '1'
def last_is_one : DFA σ  := {qs := Q, q₀ := ⟨0, by simp⟩ , fs := {⟨1 , by simp⟩} , δ := δ₁}

def w₁ : word Q := [ ⟨1 , by simp⟩, ⟨0 , by simp⟩ ]
def w₂ : word Q := [ ⟨0 , by simp⟩, ⟨1 , by simp⟩ ]
def w₃ : word Q := [ ]

#eval dfa_accepts last_is_one w₁
#eval dfa_accepts last_is_one w₂
#eval dfa_accepts last_is_one w₃

theorem accepts_suffix_1 (w : word σ) : w++[⟨1, by simp⟩] ∈ dfaLang last_is_one := by
  simp only [dfaLang,Set.mem_def]
  apply (accepts_suffix_iff last_is_one [⟨1,by simp⟩]).mpr
  intro q r
  simp [last_is_one,δ₁]
  split
  next m₁ => simp at m₁
  next _ => rfl
  next m₂ => simp at m₂
  next _ => rfl

def q₁ : Q := ⟨0, by simp⟩
def q₂ : Q := ⟨1, by simp⟩

#eval distinct_table_filling last_is_one q₁ q₂
#eval distinct_table_filling last_is_one q₁ q₁

#eval distinct last_is_one q₁ q₂
#eval distinct last_is_one q₁ q₁


-- Proof that {a^nb^n | n>=0} is not a regular language - cannot be the language of any DFA


-- Definitions
def f : Finset (Fin 2) := (Fin.fintype 2).elems

-- helper instance so that numbers can be used instead of subtypes
instance : OfNat ({x // x ∈ f}) a where
  ofNat := ⟨Fin.ofNat' a (NeZero.pos 2), by simp [f,Fintype.complete]⟩

def L : Lang f := {power [1] x ++ power [2] x | x}

example : [1,1,2,2] ∈ L := by
  simp only [L,Set.mem_def,setOf]
  exists 2

-- Proof

lemma take_power_count_eq_len [DecidableEq α] (a : α) : (n : ℕ) → {_ : m ≤ n} → ((power [a] n).take m).count a = m := by
  induction m with
  | zero => simp [List.count]
  | succ m s => intro n h
                match n with
                | 0 => trivial
                | n+1 => simp only [List.take,List.append]
                         rw [List.count_cons_self]
                         simp only [·+·,Add.add,Nat.add]
                         apply congr
                         · rfl
                         · apply s
                           exact Nat.le_of_succ_le_succ h

lemma count_append_eq (e : α) [DecidableEq α] (a b : List α) : (a++b).count e = (a++b).length → b.count e = b.length := by
  intro eq
  have : a.count e + b.count e = a.length + b.length := by
    rw [List.count_append] at eq
    rw [eq]
    simp
  have := List.count_eq_length.mp eq
  rw [List.count_eq_length]
  intro b bin
  apply this
  rw [List.mem_append]
  apply Or.inr
  exact bin


theorem power_count_eq [DecidableEq α] {a : α} (n : ℕ) : (power [a] n).count a = n := by
  induction n with
  | zero => simp [power]
  | succ n s => simp only [power,List.count_append,List.count_singleton]
                rw [s,Nat.succ_eq_add_one,Nat.add_comm]

theorem power_count_eq_zero [DecidableEq α] (a b : α) {ne : a ≠ b} (n : ℕ) : (power [a] n).count b = 0 := by
  induction n with
  | zero => simp [power]
  | succ n s => simp only [power,List.count_append,List.count_singleton]
                rw [s,List.count_singleton']
                split
                · have : b = a := by assumption
                  rw [this] at ne
                  contradiction
                · rfl

theorem mem_L_eq_count : a ∈ L → a.count 1 = a.count 2 := by
  simp only [L,Set.mem_def,setOf]
  intro ex
  apply Exists.elim ex
  intro n h
  rw [←h]
  rw [List.count_append,power_count_eq,power_count_eq_zero,List.count_append,power_count_eq_zero,power_count_eq]
  · simp
  · simp
  · simp

theorem nmem_L_neq_count : a.count 1 ≠ a.count 2 → a ∉ L := by
  apply Decidable.not_imp_not.mpr
  apply mem_L_eq_count

lemma pow_lt {a b : α} : n ≤ List.length (power [a] n ++ power [b] n) := by
  induction n with
  | zero => simp
  | succ n s => simp only [power,List.length,List.append,Nat.succ_eq_add_one]
                have : n + 1 ≤ (power [a] n ++ power [b] n).length + 1 := by
                  apply Nat.succ_le_succ
                  exact s
                apply Nat.le_trans
                · apply this
                · simp [power,Nat.le_succ]


lemma take_power_eq_first (e₁ e₂ : α) : (n m : ℕ) → (x ≤ n) → (power [e₁] n ++ power [e₂] m).take x = (power [e₁] n).take x := by
  induction x with
  | zero => simp
  | succ x s => intro n m le
                match n with
                | 0 => contradiction
                | n+1 => simp only [List.take,power,List.append,Nat.add]
                         apply congr
                         · rfl
                         apply s
                         exact Nat.succ_le_succ_iff.mp le

theorem L_not_regular : ¬ ∃ d : DFA f, dfaLang d = L := by
  intro ex
  apply Exists.elim ex
  intro d eq
  rw [Set.ext_iff] at eq
  apply Exists.elim (pumping_lemma d)
  intro n h
  have ex_split := h (power [1] n ++ power [2] n) ((eq _).mpr (by simp [L])) pow_lt
  apply Exists.elim ex_split
  intro a ex
  apply Exists.elim ex
  intro b ex
  apply Exists.elim ex
  intro c ex
  have ab_eq : a ++ b = (power [1] n).take (a.length + b.length) := by
    rw [←take_power_eq_first]
    · rw [ex.1,List.append_assoc,List.take_append]
      simp
    · exact ex.2.1
  have : (a++b).count 1 = (a++b).length := by
    nth_rewrite 1 [ab_eq]
    rw [take_power_count_eq_len]
    simp only [List.length_append]
    exact ex.2.1
  have beq : b.count 1 = b.length := count_append_eq _ _ _ this
  have bnmem : b.count 2 = 0 := by
    rw [List.count_eq_zero]
    intro twoin
    have := List.count_eq_length.mp beq 2 twoin
    contradiction
  have aeq : a.count 1 = a.length := by
    rw [List.length_append,List.count_append,Nat.add_comm] at this
    rw [←List.count_append,Nat.add_comm,←List.length_append] at this
    exact count_append_eq _ _ _ this
  have anmem : a.count 2 = 0 := by
    rw [List.count_eq_zero]
    intro twoin
    have := List.count_eq_length.mp aeq 2 twoin
    contradiction
  have count1 : (a++b++c).count 1 = n := by
    rw [←ex.1,List.count_append]
    rw [power_count_eq,power_count_eq_zero]
    · simp
    · simp
  have count2 : (a++b++c).count 2 = n := by
    rw [←ex.1,List.count_append]
    rw [power_count_eq,power_count_eq_zero]
    · simp
    · simp
  have ccount : c.count 2 = n := by
    rw [←count2,List.count_append,List.count_append,bnmem,anmem]
    simp
  have : ∃ x, (a ++ (power b x) ++ c).count 1 > (a ++ (power b x) ++ c).count 2 := by
    exists 2
    simp only [power,List.append_nil,List.count_append]
    rw [←Nat.add_assoc,Nat.add_assoc,Nat.add_assoc,←Nat.add_assoc]
    have : List.count 1 b + List.count 1 c = List.count 1 c + List.count 1 b := by apply Nat.add_comm
    rw [this,←Nat.add_assoc,←List.count_append,←List.count_append,count1]
    rw [anmem,bnmem,ccount]
    simp only [Nat.zero_add]
    rw [beq]
    have : b.length ≠ 0 := Nat.pos_iff_ne_zero.mp (List.length_pos_of_ne_nil ex.2.2.1)
    apply Nat.gt_of_not_le
    simpa
  apply Exists.elim this
  intro p h
  have := ex.2.2.2 p
  rw [eq] at this
  have : (a ++ power b p ++ c).count 1 = (a ++ power b p ++ c).count 2 := mem_L_eq_count this
  have : (a ++ power b p ++ c).count 1 ≠ (a ++ power b p ++ c).count 2 := ne_iff_lt_or_gt.mpr (Or.inr h)
  contradiction

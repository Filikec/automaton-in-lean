import Automaton.NFA.Basic
import Automaton.DFA.Minimization
import Automaton.DFA.ToNFA
import Automaton.NFA.ToDFA

-- normal automaton

open NFA DFA

def Q : Finset (Fin 2) := {0,1}
def σ : Finset (Fin 2) := {0,1}

def δ₁ : Q → σ → Finset Q
  | ⟨0, _⟩ , ⟨1,_⟩ => {⟨1,by simp⟩}
  | ⟨0, _⟩ , ⟨0,_⟩ => {⟨0,by simp⟩}
  | ⟨1, _⟩ , ⟨1,_⟩ => {⟨1,by simp⟩}
  | ⟨1, _⟩ , ⟨0,_⟩ => {⟨0,by simp⟩}

def nfa₁ : @NFA (Fin 2) (Fin 2) := {qs := Q, init := ⟨0,by simp⟩, fs := {⟨1,by simp⟩} , δ := δ₁}

def w₁ : word σ := []
def w₂ : word σ := [⟨1, by simp⟩ , ⟨0, by simp⟩]
def w₃ : word σ := [⟨0, by simp⟩ , ⟨1, by simp⟩]

#eval nfa_accepts nfa₁ w₁
#eval nfa_accepts nfa₁ w₂
#eval nfa_accepts nfa₁ w₃

#eval dfa_accepts (ToDFA.nfa_to_dfa nfa₁) w₁
#eval dfa_accepts (ToDFA.nfa_to_dfa nfa₁) w₂
#eval dfa_accepts (ToDFA.nfa_to_dfa nfa₁) w₃

#eval nfa_accepts (ToNFA.dfa_to_nfa (ToDFA.nfa_to_dfa nfa₁)) w₁
#eval nfa_accepts (ToNFA.dfa_to_nfa (ToDFA.nfa_to_dfa nfa₁)) w₂
#eval nfa_accepts (ToNFA.dfa_to_nfa (ToDFA.nfa_to_dfa nfa₁)) w₃

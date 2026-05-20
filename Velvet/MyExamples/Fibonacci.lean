import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"
set_option loom.solver "z3"

def fibonacci (a : Nat) : Nat :=
  match a with
  | 0 => 0
  | 1 => 1
  | a + 2 => fibonacci a + fibonacci (a + 1)

method fibo (a : Nat) return (res : Nat)
  ensures cost - costOld ≥ fibonacci (a + 1)
  do
  if a ≤ 1 then
    return a
  else
    let ⟨prev₁, cost'⟩ ← fibo (a - 1) cost
    let ⟨prev₂, cost''⟩ ← fibo (a - 2) cost'
    cost := cost''
    return prev₁ + prev₂

lemma fib_step (a : Nat) (h : a ≥ 1) :
    fibonacci (a + 1) = fibonacci a + fibonacci (a - 1) := by
  cases a with
  | zero => grind
  | succ a => cases a <;> simp [fibonacci]; grind

attribute [grind] fib_step
set_option maxHeartbeats 1000000

prove_correct fibo by
  loom_solve
  { simp
    cases a with
    | zero => simp [fibonacci]
    | succ b => cases b <;> try (simp [fibonacci]) <;> contradiction }
  { rcases i_2 with rfl
    rcases i_5 with rfl
    have hsum : costOld + 1 + fibonacci a + fibonacci (a - 1) ≤ i_4 := by sorry

    have hfib : fibonacci a + fibonacci (a - 1) = fibonacci (a + 1) := by
      simpa using (fib_step a (by omega)).symm

    have hfinal : costOld + 1 + fibonacci (a + 1) ≤ i_4 := by grind
    omega
    }

#eval (fibo 20 0).run
#eval fibonacci 3
#eval fibonacci 4

#eval (fibo 3 0).run
#eval fibonacci 4

#eval (fibo 4 0).run
#eval fibonacci 5

#eval (fibo 5 0).run
#eval fibonacci 6

#eval (fibo 6 0).run
#eval fibonacci 7

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

set_option linter.unusedVariables false

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

method Increment (mut x : Nat) return (u : Unit)
  require costOld = 0
  ensures cost ≥ 2
  do
  if x > 2 then
    x := x + 1
  else
    x := x + 2
  return

#print Increment

prove_correct Increment by
    loom_solve

#eval (Increment 5 0).run

method Swap (mut a : Int) (mut b : Int) return (u : Unit)
  ensures a = bOld ∧ b = aOld
  ensures cost - costOld ≥ 2 ∧ cost - costOld ≤ 2
  do
    let tmp := a
    a := b
    b := tmp
    return

#eval (Swap 4 8 0).run

prove_correct Swap by loom_solve

method incrementArray (mut arr : Array Nat) (inc : Nat) return (res : Unit)
  require costOld = 0
  ensures ∀ j < arr.size, arr[j]! = arrOld[j]! + inc
  ensures cost ≥ arr.size
  do
    let mut i := 0
    while i < arr.size
    invariant i ≤ arr.size
    invariant ∀ j < i, arr[j]! = arrOld[j]! + inc
    invariant ∀ j ≥ i, j < arr.size → arr[j]! = arrOld[j]!
    invariant cost ≥ costOld + i
    do
      arr[i] := arr[i]! + inc
      i := i + 1
    return ()

prove_correct incrementArray by
  loom_solve

#eval (incrementArray #[1, 2, 3] 2 0).run

method Factorial (n: Nat) return (res : Nat)
  ensures res > 0
  ensures cost - costOld ≤ n + 1
  do
    if n = 0 then
      return 1
    else
      let ⟨prev, cost'⟩ ← Factorial (n - 1) cost
      cost := cost'
      return n * prev

#eval (Factorial 5 0).run

set_option loom.solver "z3" in
prove_correct Factorial by
  loom_solve

-- Non-obvious termination
method GCD (a : Nat) (b : Nat) return (res : Nat)
  require a > 0
  ensures res > 0
  ensures cost - costOld <= b + 1
  do
    if b = 0 then
      return a
    else
      let remainder := a % b
      let ⟨result, cost'⟩ ← GCD b remainder cost
      return result
  termination_by b
  decreasing_by
    apply Nat.mod_lt
    grind

-- attribute [solverHint] Nat.mod_lt

#eval (GCD 124 16 0).run

prove_correct GCD
termination_by b
decreasing_by all_goals(
  apply Nat.mod_lt
  grind
  )
by
  loom_solve

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

set_option linter.unusedVariables false

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

method Minimum (a: Int) (b: Int) return (minValue: Int)
    ensures minValue ≤ a
    ensures minValue ≤ b
    ensures minValue = a ∨ minValue = b
    do
    if a <= b then
        return a
    else
        return b

#eval (Minimum 5 7 0).run

prove_correct Minimum by
  loom_solve






-- Returning tuple
method DivMod (a: Nat) (b: Nat) return (result: Nat × Nat)
    require b > 0
    ensures result.1 = a / b  -- quotient
    ensures result.2 = a % b  -- remainder
    do
    return (a / b, a % b)

#eval (DivMod 10 3 0).run

prove_correct DivMod
  by loom_solve




-- Loops
method DoubleAll (mut arr: Array Int) return (u: Unit)
    ensures arr.size = arrOld.size
    ensures ∀ i, 0 ≤ i ∧ i < arr.size → arr[i]! = 2 * arrOld[i]!
    do
    let mut i := 0
    while i < arr.size
        invariant arr.size = arrOld.size
        invariant 0 ≤ i ∧ i ≤ arr.size
        invariant ∀ k, 0 ≤ k ∧ k < i → arr[k]! = 2 * arrOld[k]!
        invariant ∀ k, i ≤ k ∧ k < arr.size → arr[k]! = arrOld[k]!
        done_with i = arr.size
    do
        arr := arr.set! i (2 * arr[i]!)
        i := i + 1
    return

#eval (DoubleAll #[1, 2, 3] 0).run

prove_correct DoubleAll
  by loom_solve

#print DoubleAll




-- Non-determinism
method PickGreater (inp: Nat) return (res: Nat)
  ensures res > inp + 10
  do
    let ans :| ans > inp + 500
    return ans

#eval (PickGreater 100 0).run

set_option loom.solver "cvc5" in
prove_correct PickGreater by
  loom_solve





def SumDigits (n: Nat): Nat :=
  if n = 0 then 0
  else (n % 10) + SumDigits (n / 10)

lemma SumDigits_unfold (n : Nat) (h : n > 0) :
  SumDigits n = (n % 10) + SumDigits (n / 10) := by
  rw [SumDigits]
  have h' : n ≠ 0 := Nat.ne_of_gt h
  simp [h']

lemma SumDigits_zero : SumDigits 0 = 0 := by
  unfold SumDigits
  simp

method SumOfDigits (number: Nat) return (sum: Nat)
    ensures sum = SumDigits number
    do
    let mut sum := 0
    let mut n := number
    while n > 0
        invariant sum + SumDigits n = SumDigits number
        invariant 0 ≤ sum
        done_with n = 0
    do
        let digit := n % 10
        sum := sum + digit
        n := n / 10
    return sum

#eval (SumOfDigits 123 0).run

attribute [grind] Nat.mod_add_div SumDigits_unfold SumDigits_zero
prove_correct SumOfDigits by
  loom_solve




set_option loom.semantics.choice "angelic" in
method ChoosePositive return (x : Int)
  ensures x > 10
do
  let x :| x > 5
  return x

#eval (ChoosePositive 0).run

prove_correct ChoosePositive by
  sorry

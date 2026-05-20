import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

set_option linter.unusedVariables false

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"
set_option loom.solver "grind"

-- division by multiple subtractions
method div_mod (mut a : Nat) (b : Nat) return (q : Nat)
  require b > 0
  ensures aOld = q * b + a
  ensures a < b
  ensures cost ≥ costOld + 3 * q
  do
    let mut q := 0
    while b ≤ a
    invariant a + q * b = aOld
    invariant cost ≥ costOld + 3 * q
    do
      a := a - b
      q := q + 1
    return q

prove_correct div_mod by
  loom_solve

#eval (div_mod 20 8 0).run





set_option loom.semantics.termination "total" in
method FactorialTotal (n: Nat) return (res: Nat)
  ensures res > 0
  do
    if n = 0 then
      return 1
    else
      let ⟨prev, cost'⟩ ← FactorialTotal (n - 1) cost
      cost := cost'
      return n * prev
  termination_by n
  decreasing_by omega -- Prove termination measure decreases

#eval (FactorialTotal 10 0).run

set_option loom.solver "cvc5" in
prove_correct FactorialTotal by
  loom_solve






-- Finding integer square root via repeated subtraction using the following identity
-- 1 + 3 + 5 + ⬝⬝⬝ + (2k - 1) = k^2
method isqrt (mut n : Nat) return (r : Nat)
  ensures r * r ≤ nOld
  ensures nOld < (r + 1) * (r + 1)
  ensures nOld = r * r + n
  ensures cost ≥ costOld + 3 * r
  do
    let mut r := 0
    let mut odd := 1
    -- odd = 2*r + 1 will be maintained

    while odd ≤ n
    invariant nOld = r * r + n
    invariant odd = 2 * r + 1
    invariant r * r ≤ nOld
    invariant cost ≥ costOld + 3 * r
    do
      n := n - odd
      r := r + 1
      odd := odd + 2

    return r

#eval (isqrt 25 0).run

prove_correct isqrt by
  loom_solve
















set_option loom.semantics.termination "total" in
method CountDown (n: Nat) return (res: Nat)
  ensures res = 0
  do
    let mut i := n
    while i > 0
      invariant 0 ≤ i
      invariant i ≤ n
      decreasing i  -- Termination measure
    do
      i := i - 1
    return i

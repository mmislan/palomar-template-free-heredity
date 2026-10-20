module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Literal beta4m branching witness and one-species upper operator.
All daughter counts, including below16, remain in the moments. This defines
the new witness independently; no beta8m success theorem is imported.
Pending strict verification after the active reset window. -/

@[expose] public section
namespace P161Formal
open scoped BigOperators

def branchingReciprocalFiveQ (a : ℕ) : ℚ :=
  1 / (((a : ℚ)+1)*(a+2)*(a+3)*(a+4)*(a+5))

def branchingAQ (a : ℕ) : ℚ :=
  if a ≤ 12 then (1275068416 / 16120377) * (3/4)^a
  else 1860480 * branchingReciprocalFiveQ a

def branchingFuelCorrectionQ (a : ℕ) : ℚ :=
  if a = 0 then -branchingAQ 0 / 2 else branchingAQ a * min (6*a) 70

def branchingWitnessQ (a : ℕ) (fuel : Bool) : ℚ :=
  branchingAQ a + if fuel then 0 else branchingFuelCorrectionQ a / 4000000

def branchingMomentQ (a : ℕ) (fuel : Bool) : ℚ :=
  ∑ k ∈ Finset.range (a+1), ((a.choose k : ℕ) : ℚ) / 2^a * branchingWitnessQ k fuel

/-- `U` and `v` are the actual foreign normalized count and excess consumption
loads; the physical source must establish0<=U<=2 and0<=v<=1843200. -/
def branchingSiteOperatorQ (a : ℕ) (fuel : Bool) (U v seed : ℚ) : ℚ :=
  let u := (a : ℚ)/2048
  let current := branchingWitnessQ a fuel
  let chem := seed*(1-u)*(branchingWitnessQ (a+1) fuel-current) +
    (a : ℚ)*(branchingWitnessQ (a-1) fuel-current)
  if fuel then
    chem + 800*a*(1-u)*(branchingWitnessQ (a+1) false-current) +
      400*a*(branchingWitnessQ (a-1) false-current) +
      (4000000*(1+u+U)+v)*(branchingWitnessQ a false-current) +
      branchingMomentQ a false + branchingMomentQ a true - 2*current +
      (u+U)*(2*branchingMomentQ a false-current)
  else
    chem + 4000000*(branchingWitnessQ a true-current) +
      2*branchingMomentQ a false - 2*current

end P161Formal

module

public import P161Formal.BranchingProfile
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr

/-! Rational adapter of the reciprocal-factorial argument in the preserved
FunctionalCapacity/Cert.lean, through binE_hh only. No beta8m parameter or
mission declaration is imported. This bounds complete binomial moments,
including daughter counts below16. -/

@[expose] public section
namespace P161Formal
open scoped BigOperators

theorem branching_reciprocal_positive (a : ℕ) : 0 < branchingReciprocalFiveQ a := by
  unfold branchingReciprocalFiveQ
  positivity

theorem branching_reciprocal_factorial (a : ℕ) :
    branchingReciprocalFiveQ a = (a.factorial : ℚ)/(a+5).factorial := by
  have hf : (a+5).factorial =
      (a+5)*((a+4)*((a+3)*((a+2)*((a+1)*a.factorial)))) := by
    simp only [Nat.factorial_succ]
  rw [hf]
  unfold branchingReciprocalFiveQ
  push_cast
  have h : (a.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
  field_simp

theorem branching_choose_reciprocal {a k : ℕ} (hk : k ≤ a) :
    (a.choose k : ℚ)*branchingReciprocalFiveQ k =
      branchingReciprocalFiveQ a*((a+5).choose (k+5) : ℚ) := by
  rw [branching_reciprocal_factorial,branching_reciprocal_factorial,
    Nat.cast_choose ℚ hk,Nat.cast_choose ℚ (show k+5 ≤ a+5 by omega),
    show a+5-(k+5) = a-k by omega]
  have h1 : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have h2 : ((k+5).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k+5)
  have h3 : (a.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
  have h4 : ((a+5).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (a+5)
  have h5 : ((a-k).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (a-k)
  field_simp

theorem branching_shifted_choose_sum (a : ℕ) :
    ∑ k ∈ Finset.range (a+1), (a+5).choose (k+5) ≤ 2^(a+5) := by
  rw [← Nat.sum_range_choose (a+5),show a+5+1 = 5+(a+1) by omega,
    Finset.sum_range_add _ 5 (a+1)]
  refine le_trans (le_of_eq ?_) (Nat.le_add_left _ _)
  exact Finset.sum_congr rfl (fun k _ => by rw [add_comm k 5])

theorem branching_binomial_reciprocal (a : ℕ) :
    (∑ k ∈ Finset.range (a+1), (a.choose k : ℚ)/2^a*branchingReciprocalFiveQ k) ≤
      32*branchingReciprocalFiveQ a := by
  have he (k : ℕ) (hk : k ∈ Finset.range (a+1)) :
      (a.choose k : ℚ)/2^a*branchingReciprocalFiveQ k =
        branchingReciprocalFiveQ a/2^a*((a+5).choose (k+5) : ℚ) := by
    rw [div_mul_eq_mul_div,branching_choose_reciprocal
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
    ring
  rw [Finset.sum_congr rfl he,← Finset.mul_sum]
  have hs : (∑ k ∈ Finset.range (a+1), ((a+5).choose (k+5) : ℚ)) ≤ 2^(a+5) := by
    exact_mod_cast branching_shifted_choose_sum a
  have hp := (branching_reciprocal_positive a).le
  calc
    _ ≤ branchingReciprocalFiveQ a/2^a*2^(a+5) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = 32*branchingReciprocalFiveQ a := by
      rw [pow_add,div_mul_eq_mul_div,div_eq_iff (by positivity)]
      ring

end P161Formal

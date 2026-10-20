module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Lean.Elab.Tactic.Omega

/-!
Soundness of the exact coefficient recurrence used by the finite paired-floor
moment checker. Each list element is used once. This is a structural proof for
every list and parent count; no generator termination/coverage is assumed.
The actual full literal-data residual checks remain separate.
-/

@[expose] public section
namespace P161Formal
open scoped BigOperators

def nextBinomial (a k c : ℕ) : ℕ := c * (a - k) / (k + 1)

theorem next_binomial_correct (a k : ℕ) :
    nextBinomial a k (a.choose k) = a.choose (k + 1) := by
  unfold nextBinomial
  rw [← Nat.choose_succ_right_eq]
  exact Nat.mul_div_cancel _ (Nat.succ_pos k)

/-- Linear traversal of the weights, with exact integer coefficient updates. -/
def binomialFold (a k c : ℕ) : List ℕ → ℕ
  | [] => 0
  | v :: rest => c * v + binomialFold a (k + 1) (nextBinomial a k c) rest

/-- Independent specification using mathematical binomial coefficients. -/
def binomialSpecification (a k : ℕ) : List ℕ → ℕ
  | [] => 0
  | v :: rest => a.choose k * v + binomialSpecification a (k + 1) rest

theorem binomial_fold_correct (a k : ℕ) (weights : List ℕ) :
    binomialFold a k (a.choose k) weights = binomialSpecification a k weights := by
  induction weights generalizing k with
  | nil => rfl
  | cons v rest ih =>
      simp only [binomialFold, binomialSpecification, next_binomial_correct, ih]

theorem binomial_specification_sum (a k : ℕ) (weights : List ℕ) :
    binomialSpecification a k weights =
      ∑ i ∈ Finset.range weights.length, a.choose (k + i) * weights[i]?.getD 0 := by
  induction weights generalizing k with
  | nil => simp [binomialSpecification]
  | cons v rest ih =>
      simp only [binomialSpecification, List.length_cons, Finset.sum_range_succ',
        List.getElem?_cons_zero, Option.getD_some, Nat.add_zero]
      rw [ih]
      rw [Nat.add_comm (a.choose k * v)]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp [Nat.add_left_comm, Nat.add_comm]

def binomialSeed16 (a : ℕ) : ℕ := a.descFactorial 16 / Nat.factorial 16

theorem binomial_seed16_correct (a : ℕ) : binomialSeed16 a = a.choose 16 := by
  exact (Nat.choose_eq_descFactorial_div_factorial a 16).symm

/-- Length a-31 includes precisely counts16,...,a-16. Both floor boundaries
are included, including the single possible count at parent32. -/
def pairedWeights (profile : List ℕ) (a : ℕ) : List ℕ :=
  if a < 32 then [] else (profile.drop 16).take (a - 31)

def pairedMomentNumerator (profile : List ℕ) (a : ℕ) : ℕ :=
  binomialFold a 16 (binomialSeed16 a) (pairedWeights profile a)

theorem paired_moment_correct (profile : List ℕ) (a : ℕ) :
    pairedMomentNumerator profile a =
      binomialSpecification a 16 (pairedWeights profile a) := by
  unfold pairedMomentNumerator
  rw [binomial_seed16_correct, binomial_fold_correct]

theorem paired_weights_length (profile : List ℕ) (a : ℕ)
    (ha : 32 ≤ a) (hsize : a + 1 ≤ profile.length) :
    (pairedWeights profile a).length = a - 31 := by
  simp only [pairedWeights, ite_eq_right (by omega : ¬a < 32), List.length_take,
    List.length_drop]
  omega

end P161Formal

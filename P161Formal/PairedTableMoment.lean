module

public import P161Formal.ResetChecker
public import P161Formal.RecoveryProfile
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Push

/-! Mathematical meaning of the already checked integer paired moment.
The range is exactly16,...,a-16, including both boundaries. No reset rows are
recomputed here and the moment is not extended to inadmissible daughter marks. -/

@[expose] public section
namespace P161Formal
open scoped BigOperators

theorem paired_weights_get (profile : List ℕ) (a i : ℕ)
    (ha : 32 ≤ a) (hi : i < a-31) :
    (pairedWeights profile a)[i]?.getD 0 = profile[16+i]?.getD 0 := by
  simp only [pairedWeights,ite_eq_right (show ¬a < 32 by omega),
    List.getElem?_take_of_lt hi,List.getElem?_drop]

theorem full_profile_zero_lookup (a : ℕ) :
    fullProfileFuelZero[a]?.getD 0 = (fullProfilePairs[a]?.getD (0,0)).1 := by
  simp only [fullProfileFuelZero,List.getElem?_map]
  cases fullProfilePairs[a]? <;> rfl

def pairedTableMomentQ (a : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (a-31),
    (a.choose (16+i) : ℚ)/2^a*profileEntryQ (16+i) false

theorem paired_table_moment_eq (a : ℕ) (hb : a ≤ 2048) :
    (pairedMomentNumerator fullProfileFuelZero a : ℚ)/(2^a*10^18) =
      pairedTableMomentQ a := by
  by_cases ha : 32 ≤ a
  · have hsize : a+1 ≤ fullProfileFuelZero.length := by
      rw [fullProfileFuelZero,List.length_map,full_profile_length]
      omega
    rw [paired_moment_correct,binomial_specification_sum,
      paired_weights_length fullProfileFuelZero a ha hsize]
    push_cast
    rw [Finset.sum_div]
    unfold pairedTableMomentQ
    apply Finset.sum_congr rfl
    intro i hi
    rw [paired_weights_get fullProfileFuelZero a i ha (Finset.mem_range.mp hi),
      full_profile_zero_lookup]
    simp only [profileEntryQ,Bool.false_eq_true,ite_false]
    ring
  · have hnot : a < 32 := by omega
    have hzero : a-31 = 0 := by omega
    simp [pairedMomentNumerator,pairedWeights,hnot,binomialFold,pairedTableMomentQ,hzero]

end P161Formal

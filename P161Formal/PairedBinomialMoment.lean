module

public import P161Formal.PairedTableMoment
public import P161Formal.LiteralTableBridge
public import Mathlib.Algebra.BigOperators.Intervals

/-! The checked paired moment as a binomial expectation, including symmetry
of the same actual complementary split. Both16 floors remain in the mask. -/

@[expose] public section
namespace P161Formal
open scoped BigOperators
noncomputable section

def pairedBinomialMoment (f : ℕ → ℝ) (a : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (a+1),
    (a.choose k : ℝ)/2^a*(if 16 ≤ k ∧ 16 ≤ a-k then f k else 0)

theorem paired_interval_sum (f : ℕ → ℝ) (a : ℕ) :
    (∑ i ∈ Finset.range (a-31), f (16+i)) =
      ∑ k ∈ Finset.range (a+1), if 16 ≤ k ∧ 16 ≤ a-k then f k else 0 := by
  rw [←Finset.sum_filter]
  apply Finset.sum_bij (fun i _ => 16+i)
  · intro i hi
    have hi' := Finset.mem_range.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by omega⟩
  · intro i hi k hk heq
    omega
  · intro k hk
    obtain ⟨hkr,hfloor⟩ := Finset.mem_filter.mp hk
    have hk' := Finset.mem_range.mp hkr
    exact ⟨k-16,Finset.mem_range.mpr (by omega),by omega⟩
  · intro i hi
    rfl

theorem paired_table_moment_real_sum (a : ℕ) :
    (pairedTableMomentQ a : ℝ) =
      ∑ i ∈ Finset.range (a-31),
        (a.choose (16+i) : ℝ)/2^a*profileEntry (16+i) false := by
  have hpow : ((2^a : ℚ) : ℝ) = (2 : ℝ)^a := by
    simpa only [Rat.coe_castHom,Rat.cast_ofNat] using map_pow (Rat.castHom ℝ) (2 : ℚ) a
  change (Rat.castHom ℝ) (∑ i ∈ Finset.range (a-31),
    (a.choose (16+i) : ℚ)/2^a*profileEntryQ (16+i) false) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Rat.coe_castHom,Rat.cast_mul,Rat.cast_div,Rat.cast_natCast,hpow,profileEntry]

theorem paired_table_moment_as_binomial (a : ℕ) :
    (pairedTableMomentQ a : ℝ) = pairedBinomialMoment (fun k => profileEntry k false) a := by
  rw [paired_table_moment_real_sum,paired_interval_sum
    (fun k => (a.choose k : ℝ)/2^a*profileEntry k false) a]
  simp only [pairedBinomialMoment,mul_ite,mul_zero]

theorem paired_binomial_complement (f : ℕ → ℝ) (a : ℕ) :
    (∑ k ∈ Finset.range (a+1),
      (a.choose k : ℝ)/2^a*(if 16 ≤ k ∧ 16 ≤ a-k then f (a-k) else 0)) =
        pairedBinomialMoment f a := by
  unfold pairedBinomialMoment
  rw [←Finset.sum_range_reflect (fun k =>
    (a.choose k : ℝ)/2^a*(if 16 ≤ k ∧ 16 ≤ a-k then f (a-k) else 0)) (a+1)]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ a := by have h := Finset.mem_range.mp hk; omega
  have hinv : a-(a-k) = k := by omega
  simp only [Nat.add_sub_cancel,hinv,Nat.choose_symm hk',and_comm]

end
end P161Formal

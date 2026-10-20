module

public import P161Formal.RecoveryProfile
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
Uniform geometric-tail enclosure, intended to replace repeated high-count
fraction comparisons above1166. The literal suffix identity is still checked
in the kernel. This source is a pending independent branch until its own strict
receipt exists; do not run it during the sealed reset window.
-/

@[expose] public section
namespace P161Formal

set_option exponentiation.threshold 2048

def recoveryTailCoefficientQ (a : ℕ) : ℚ := (258 + recoveryTailKQ a) / 8000000

theorem recovery_tail_geometric (a : ℕ) (ha : 768 ≤ a) :
    recoveryTailAQ a = recoveryTailAQ 768 * (10 / 11 : ℚ) ^ (a - 768) := by
  by_cases h : a = 768
  · subst a
    simp
  · have hn : ¬ a ≤ 768 := by omega
    simp only [recoveryTailAQ, recoveryTailQ, ite_eq_right hn,
      Nat.le_refl, ite_true]
    ring

theorem recovery_geometric_tail_positive (a : ℕ) (ha : 768 ≤ a) :
    0 < recoveryTailAQ a := by
  rw [recovery_tail_geometric a ha]
  apply mul_pos
  · norm_num [recoveryTailAQ, recoveryTailQ, cubicRecoveryTailQ]
  · exact pow_pos (by norm_num : (0 : ℚ) < 10 / 11) _

theorem recovery_geometric_antitone (a b : ℕ) (ha : 768 ≤ a) (hab : a ≤ b) :
    recoveryTailAQ b ≤ recoveryTailAQ a := by
  have he : b - 768 = (a - 768) + (b - a) := by omega
  have hid : recoveryTailAQ b = recoveryTailAQ a * (10 / 11 : ℚ) ^ (b - a) := by
    rw [recovery_tail_geometric b (by omega), recovery_tail_geometric a ha, he, pow_add]
    ring
  have hp : (10 / 11 : ℚ) ^ (b - a) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  rw [hid]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp
    (le_of_lt (recovery_geometric_tail_positive a ha))

theorem recovery_tail_coefficient_bounds (a : ℕ) (ha : 768 ≤ a) (hb : a ≤ 2048) :
    0 < recoveryTailCoefficientQ a ∧ recoveryTailCoefficientQ a < 1 / 10000 := by
  have har : (768 : ℚ) ≤ a := by exact_mod_cast ha
  have hbr : (a : ℚ) ≤ 2048 := by exact_mod_cast hb
  simp only [recoveryTailCoefficientQ, recoveryTailKQ,
    ite_eq_right (show ¬ a < 768 by omega)]
  constructor <;> nlinarith

theorem recovery_tail_delta_factor (a : ℕ) :
    recoveryTailDeltaQ a = recoveryTailAQ a * recoveryTailCoefficientQ a := by
  unfold recoveryTailDeltaQ recoveryTailCoefficientQ
  ring

theorem recovery_base_geometric_bounds (a : ℕ) (fuel : Bool)
    (ha : 768 ≤ a) (hb : a ≤ 2048) :
    0 < recoveryBaseQ a fuel ∧ recoveryBaseQ a fuel ≤ recoveryTailAQ a := by
  have hA := recovery_geometric_tail_positive a ha
  obtain ⟨hc0, hc1⟩ := recovery_tail_coefficient_bounds a ha hb
  cases fuel
  · simpa [recoveryBaseQ] using And.intro hA (le_refl (recoveryTailAQ a))
  · change 0 < recoveryTailAQ a - recoveryTailDeltaQ a ∧
      recoveryTailAQ a - recoveryTailDeltaQ a ≤ recoveryTailAQ a
    rw [recovery_tail_delta_factor]
    constructor <;> nlinarith

set_option exponentiation.threshold 2048 in
theorem recovery_tail_cut_below_grid : recoveryTailAQ 1166 ≤ (1 / 10^18 : ℚ) := by
  norm_num [recoveryTailAQ, recoveryTailQ, cubicRecoveryTailQ]

theorem recovery_geometric_tail_below_grid (a : ℕ) (ha : 1166 ≤ a) :
    recoveryTailAQ a ≤ (1 / 10^18 : ℚ) := by
  have hdecomp : a - 768 = (1166 - 768) + (a - 1166) := by omega
  have heq : recoveryTailAQ a = recoveryTailAQ 1166 * (10 / 11 : ℚ) ^ (a - 1166) := by
    rw [recovery_tail_geometric a (by omega),
      recovery_tail_geometric 1166 (by decide), hdecomp, pow_add]
    ring
  have hpow : (10 / 11 : ℚ) ^ (a - 1166) ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have hprod := mul_le_mul_of_nonneg_left hpow
    (le_of_lt (recovery_geometric_tail_positive 1166 (by decide)))
  rw [heq]
  exact le_trans (by simpa only [mul_one] using hprod) recovery_tail_cut_below_grid

set_option maxRecDepth 32768 in
set_option maxHeartbeats 800000 in
theorem recovery_tail_grid_suffix :
    fullProfilePairs.drop 1166 = List.replicate 884 (1, 1) := by decide

theorem recovery_tail_grid_entry (a : ℕ) (fuel : Bool)
    (ha : 1166 ≤ a) (hb : a ≤ 2048) : profileEntryQ a fuel = (1 / 10^18 : ℚ) := by
  have hi : a - 1166 < 884 := by omega
  have hindex : 1166 + (a - 1166) = a := by omega
  have hrow := congrArg (fun xs : List (ℕ × ℕ) => xs[a - 1166]?.getD (0, 0))
    recovery_tail_grid_suffix
  simp only [List.getElem?_drop, List.getElem?_replicate_of_lt hi,
    Option.getD_some, hindex] at hrow
  simp only [profileEntryQ, hrow]
  cases fuel <;> norm_num

theorem recovery_tail_enclosure_above_cut (a : ℕ) (fuel : Bool)
    (ha : 1166 ≤ a) (hb : a ≤ 2048) : checkTailEnclosure a fuel = true := by
  obtain ⟨hbase0, hbaseA⟩ := recovery_base_geometric_bounds a fuel (by omega) hb
  have hA := recovery_geometric_tail_below_grid a ha
  simp only [checkTailEnclosure, decide_eq_true_eq,
    recovery_tail_grid_entry a fuel ha hb, sub_self]
  exact ⟨le_of_lt hbase0, le_trans hbaseA hA⟩

end P161Formal

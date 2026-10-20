module

public import P161Formal.PairedTableMoment
public import P161Formal.LiteralTableBridge
public import P161Formal.ResetCertificate
public import P161Formal.ResetCheckerSoundness
public import P161Formal.StrongResetAggregation
import all P161Formal.ResetAggregation

/-! The full C11 row certificate, interpreted as real paired-daughter residuals.
No finite row is replayed. The source reset operator must still be bounded by
these paired moments while retaining the actual complementary-floor test. -/

@[expose] public section
namespace P161Formal
noncomputable section

abbrev pairedTableMoment (a : ℕ) : ℝ := pairedTableMomentQ a

theorem paired_table_moment_real_eq (a : ℕ) (hb : a ≤ 2048) :
    (pairedMomentNumerator fullProfileFuelZero a : ℝ)/(2^a*10^18) =
      pairedTableMoment a := by
  have hpow : ((2^a : ℚ) : ℝ) = (2 : ℝ)^a := by
    simpa only [Rat.coe_castHom,Rat.cast_ofNat] using map_pow (Rat.castHom ℝ) (2 : ℚ) a
  have hden : ((10^18 : ℚ) : ℝ) = (10 : ℝ)^18 := by norm_num
  have h := congrArg (fun q : ℚ => (q : ℝ)) (paired_table_moment_eq a hb)
  simpa only [Rat.cast_div,Rat.cast_natCast,Rat.cast_mul,hpow,hden] using h

def resetParentRateBound (a : ℕ) (fuel : Bool) : ℝ :=
  if fuel then 3+(a : ℝ)/2048 else 1

def resetTableGain (a : ℕ) (fuel : Bool) : ℝ :=
  2*resetParentRateBound a fuel*pairedTableMoment a

theorem global_reset_table_residual (a : ℕ) (fuel : Bool)
    (ha : 16 ≤ a) (hb : a ≤ 2048) :
    resetTableGain a fuel-strongResetD*resetTableLower a fuel ≤ resetAll := by
  have h := checked_reset_row_sound a fuel 3343277526704540851 125000000000000000
    (by norm_num) (all_global_reset_rows a fuel ha hb)
  dsimp only at h
  rw [paired_table_moment_real_eq a hb] at h
  cases fuel <;>
    norm_num [resetTableGain,resetParentRateBound,resetTableLower,strongResetD,resetAll] at h ⊢
  all_goals convert h using 1 <;> ring

theorem deficient_reset_table_residual (a : ℕ) (fuel : Bool)
    (ha : 16 ≤ a) (hb : a < 512) :
    resetTableGain a fuel-strongResetD*resetTableLower a fuel ≤ resetLow := by
  have h := checked_reset_row_sound a fuel (-147104211175367700201) 500000000000000000
    (by norm_num) (all_deficient_reset_rows a fuel ha hb)
  dsimp only at h
  rw [paired_table_moment_real_eq a (by omega)] at h
  cases fuel <;>
    norm_num [resetTableGain,resetParentRateBound,resetTableLower,strongResetD,resetLow] at h ⊢
  all_goals convert h using 1 <;> ring

end
end P161Formal

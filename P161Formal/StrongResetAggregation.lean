module

public import P161Formal.ResetAggregation

/-! The unchanged C11 row certificate also supports A-(15/8)Delta.
Only the comparison factor changes to9993/10000. The source reset-gain
inequality remains explicit until its physical-mark bridge is discharged. -/

@[expose] public section
namespace P161Formal
open scoped BigOperators
noncomputable section

def strongResetEll : ℝ := 9993 / 10000
def strongResetD : ℝ := 93867565097 / 200000000
def strongResetDirect : ℝ := 95466445097 / 199860000

theorem strong_direct_reset_bound (X h Y : Fin 12 → ℝ) (B : ℝ) (k : Fin 12)
    (hX : ∀ i, strongResetEll * X i ≤ h i)
    (hpos : 0 < ∑ i, h i)
    (hlow : Y k - strongResetD * X k ≤ resetLow)
    (hall : ∀ i, Y i - strongResetD * X i ≤ resetAll)
    (hsource : B ≤ 8 * (∑ i, h i) + ∑ i, Y i) :
    B ≤ strongResetDirect * (∑ i, h i) ∧ B < 478 * (∑ i, h i) := by
  have hres := twelve_residuals (fun i => Y i - strongResetD * X i) k hlow hall
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hres
  have hcomp := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 12))) => hX i)
  rw [← Finset.mul_sum] at hcomp
  have hsign : resetLow + 11 * resetAll < 0 := by
    rw [signed_residual_margin]
    norm_num
  have hell : 0 < strongResetEll := by norm_num [strongResetEll]
  have hd : 0 < strongResetD := by norm_num [strongResetD]
  have hmul := mul_le_mul_of_nonneg_left hcomp (le_of_lt (div_pos hd hell))
  have hcancel : strongResetD / strongResetEll * strongResetEll = strongResetD :=
    div_mul_cancel₀ _ (ne_of_gt hell)
  have hgain : ∑ i, Y i ≤ strongResetD / strongResetEll * (∑ i, h i) := by
    nlinarith [hcancel]
  have hid : 8 + strongResetD / strongResetEll = strongResetDirect := by
    norm_num [strongResetD, strongResetEll, strongResetDirect]
  have hbound : B ≤ strongResetDirect * (∑ i, h i) := by
    rw [← hid]
    nlinarith
  refine ⟨hbound, lt_of_le_of_lt hbound ?_⟩
  have hgap : strongResetDirect < 478 := by norm_num [strongResetDirect]
  exact mul_lt_mul_of_pos_right hgap hpos

end
end P161Formal

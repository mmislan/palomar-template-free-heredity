module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
The signed finite-row aggregation in manuscript C.3.1. The row certificates and
the physical reset gain estimate are explicit hypotheses of this local lemma.
Their literal-data verification and source-operator bridge remain obligations;
this module does not assert the P161 probability theorem.
-/

public section

namespace P161Formal

open scoped BigOperators
noncomputable section

def resetD : ℝ := 93867565097 / 200000000
def resetEll : ℝ := 9997 / 10000
def resetLow : ℝ := -(147104211175367700201 / 500000000000000000)
def resetAll : ℝ := 3343277526704540851 / 125000000000000000
def resetDirect : ℝ := 95467085097 / 199940000

theorem signed_residual_margin :
    resetLow + 11 * resetAll = -(367902757 / 500000000000000000) := by
  norm_num [resetLow, resetAll]

theorem reset_direct_identity : 8 + resetD / resetEll = resetDirect := by
  norm_num [resetD, resetEll, resetDirect]

theorem reset_direct_gap : 478 - resetDirect = 104234903 / 199940000 := by
  norm_num [resetDirect]

/-- One deficient coordinate and eleven unrestricted rows. -/
theorem twelve_residuals (R : Fin 12 → ℝ) (k : Fin 12)
    (hlow : R k ≤ resetLow) (hall : ∀ i, R i ≤ resetAll) :
    ∑ i, R i ≤ resetLow + 11 * resetAll := by
  classical
  have hpoint : ∀ i, R i ≤ resetAll + if i = k then resetLow - resetAll else 0 := by
    intro i
    by_cases h : i = k
    · subst i
      simpa using hlow
    · simpa [h] using hall i
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 12))) => hpoint i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hsum
  norm_num at hsum
  linarith

/-- Analytic reset soundness after the finite rows and source gain are proved. -/
theorem direct_reset_bound (X h Y : Fin 12 → ℝ) (B : ℝ) (k : Fin 12)
    (hX : ∀ i, resetEll * X i ≤ h i)
    (hpos : 0 < ∑ i, h i)
    (hlow : Y k - resetD * X k ≤ resetLow)
    (hall : ∀ i, Y i - resetD * X i ≤ resetAll)
    (hsource : B ≤ 8 * (∑ i, h i) + ∑ i, Y i) :
    B ≤ resetDirect * (∑ i, h i) ∧ B < 478 * (∑ i, h i) := by
  have hres := twelve_residuals (fun i => Y i - resetD * X i) k hlow hall
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hres
  have hcomp := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 12))) => hX i)
  rw [← Finset.mul_sum] at hcomp
  have hsign : resetLow + 11 * resetAll < 0 := by
    rw [signed_residual_margin]
    norm_num
  have hell : 0 < resetEll := by norm_num [resetEll]
  have hd : 0 < resetD := by norm_num [resetD]
  have hmul := mul_le_mul_of_nonneg_left hcomp (le_of_lt (div_pos hd hell))
  have hcancel : resetD / resetEll * resetEll = resetD := by
    exact div_mul_cancel₀ resetD (ne_of_gt hell)
  have hgain : ∑ i, Y i ≤ resetD / resetEll * (∑ i, h i) := by
    nlinarith [hcancel]
  have hbound : B ≤ resetDirect * (∑ i, h i) := by
    rw [← reset_direct_identity]
    nlinarith
  refine ⟨hbound, lt_of_le_of_lt hbound ?_⟩
  have hgap : resetDirect < 478 := by norm_num [resetDirect]
  exact mul_lt_mul_of_pos_right hgap hpos

end
end P161Formal

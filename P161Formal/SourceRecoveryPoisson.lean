module

public import P161Formal.SourceRecoveryWitness
public import P161Formal.SubmarkovCountedWords
public import P161Formal.StrongRecoveryArithmetic

/-! Uniform low-reset Poisson-word estimate for the literal stopped source
suboperators. This is an operator estimate; the physical path event and
conditional stopping-time probability interpretation remain separate. -/

@[expose] public section
namespace P161Formal
open scoped BigOperators
noncomputable section

def recoveryWordA : ℝ := 1-strongKilledGamma/recoveryLambda
def recoveryWordB : ℝ := 478/recoveryLambda

theorem source_recovery_potential_max (x : RecoverySource) :
    sourcePotential strongRecoveryWitness x ≤ (338971453059/125000 : ℝ) := by
  rw [source_selected_potential_eq]
  have h := (Rat.cast_le (K := ℝ)).mpr (strong_population_max (sourcePopulation x))
  simpa only [Rat.cast_div,Rat.cast_ofNat] using h

theorem source_low_reset_word_bound (x : RecoverySource) :
    (∑ j ∈ Finset.range 28,
      submarkovPoissonMass recoveryNonresetOperator recoveryResetOperator
        (sourcePotential strongRecoveryWitness) (recoveryLambda/2) j x) ≤ (2/1000000 : ℝ) := by
  have ha : 0 ≤ recoveryWordA := by norm_num [recoveryWordA,strongKilledGamma]
  have hb : 0 ≤ recoveryWordB := by norm_num [recoveryWordB]
  have hmu : 0 ≤ recoveryLambda/2 := by norm_num
  have hAU (s : RecoverySource) :
      recoveryNonresetOperator.P (sourcePotential strongRecoveryWitness) s ≤
        recoveryWordA*sourcePotential strongRecoveryWitness s := by
    simpa only [recoveryWordA,strongKilledGamma] using recovery_nonreset_witness s
  have hBU (s : RecoverySource) :
      recoveryResetOperator.P (sourcePotential strongRecoveryWitness) s ≤
        recoveryWordB*sourcePotential strongRecoveryWitness s := recovery_reset_witness s
  have hprod : (recoveryLambda/2)*(recoveryWordA-1) = -(strongKilledGamma/2) := by
    norm_num [recoveryWordA,strongKilledGamma]
  have hreset : (recoveryLambda/2)*recoveryWordB = 239 := by norm_num [recoveryWordB]
  have hj (j : ℕ) :
      submarkovPoissonMass recoveryNonresetOperator recoveryResetOperator
        (sourcePotential strongRecoveryWitness) (recoveryLambda/2) j x ≤
          (Real.exp (-(strongKilledGamma/2))*(239 : ℝ)^j/j.factorial)*
            sourcePotential strongRecoveryWitness x := by
    have h := submarkov_poisson_count_bound recoveryNonresetOperator recoveryResetOperator
      (sourcePotential strongRecoveryWitness) recoveryWordA recoveryWordB (recoveryLambda/2)
      source_selected_potential_nonnegative ha hb hmu hAU hBU j x
    rwa [hprod,hreset] at h
  let P : ℝ := Real.exp (-(strongKilledGamma/2))*(∑ j ∈ Finset.range 28, (239 : ℝ)^j/j.factorial)
  have hP : 0 ≤ P := by unfold P; positivity
  calc
    _ ≤ ∑ j ∈ Finset.range 28,
        (Real.exp (-(strongKilledGamma/2))*(239 : ℝ)^j/j.factorial)*
          sourcePotential strongRecoveryWitness x :=
      Finset.sum_le_sum (fun j _ => hj j)
    _ = P*sourcePotential strongRecoveryWitness x := by
      unfold P
      rw [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ P*(338971453059/125000 : ℝ) :=
      mul_le_mul_of_nonneg_left (source_recovery_potential_max x) hP
    _ = strongWordNumerator/Real.exp (strongKilledGamma/2) := by
      unfold P strongWordNumerator
      rw [Real.exp_neg]
      ring
    _ ≤ 2/1000000 := strong_low_words_le_two_millionths

end
end P161Formal

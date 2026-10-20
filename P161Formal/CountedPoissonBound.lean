module

public import P161Formal.PoissonWords
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-! Convergent Poisson comparison for the positive counted reset words.
The input bounds are operator inequalities, not a supplied source success
probability. Source subkernels and the stopped event still require docking. -/

@[expose] public section
namespace P161Formal
open scoped BigOperators
noncomputable section

theorem finite_row_nonnegative {S : Type} [Fintype S]
    (K : S → S → ℝ) (f : S → ℝ)
    (hK : ∀ s t, 0 ≤ K s t) (hf : ∀ t, 0 ≤ f t) (s : S) :
    0 ≤ finiteRowApply K f s :=
  Finset.sum_nonneg (fun t _ => mul_nonneg (hK s t) (hf t))

theorem counted_word_nonnegative {S : Type} [Fintype S]
    (A B : S → S → ℝ) (U : S → ℝ)
    (hA : ∀ s t, 0 ≤ A s t) (hB : ∀ s t, 0 ≤ B s t)
    (hU : ∀ s, 0 ≤ U s) (n j : ℕ) (s : S) :
    0 ≤ countedWordMass A B U n j s := by
  induction n generalizing j s with
  | zero => cases j <;> simp [countedWordMass,hU]
  | succ n ih =>
      cases j with
      | zero => exact finite_row_nonnegative A _ hA (fun t => ih 0 t) s
      | succ j =>
        exact add_nonneg
          (finite_row_nonnegative A _ hA (fun t => ih (j+1) t) s)
          (finite_row_nonnegative B _ hB (fun t => ih j t) s)

def countedPoissonMass {S : Type} [Fintype S]
    (A B : S → S → ℝ) (U : S → ℝ) (mu : ℝ) (j : ℕ) (s : S) : ℝ :=
  ∑' n, (Real.exp (-mu)*mu^n/n.factorial)*countedWordMass A B U n j s

theorem counted_poisson_bound {S : Type} [Fintype S]
    (A B : S → S → ℝ) (U : S → ℝ) (a b mu : ℝ)
    (hA : ∀ s t, 0 ≤ A s t) (hB : ∀ s t, 0 ≤ B s t)
    (hU : ∀ s, 0 ≤ U s) (ha : 0 ≤ a) (hb : 0 ≤ b) (hmu : 0 ≤ mu)
    (hAU : ∀ s, finiteRowApply A U s ≤ a*U s)
    (hBU : ∀ s, finiteRowApply B U s ≤ b*U s) (j : ℕ) (s : S) :
    countedPoissonMass A B U mu j s ≤
      (Real.exp (mu*(a-1))*(mu*b)^j/j.factorial)*U s := by
  have hp (n : ℕ) : 0 ≤ Real.exp (-mu)*mu^n/n.factorial := by positivity
  have hnonneg (n : ℕ) :
      0 ≤ (Real.exp (-mu)*mu^n/n.factorial)*countedWordMass A B U n j s :=
    mul_nonneg (hp n) (counted_word_nonnegative A B U hA hB hU n j s)
  have hle (n : ℕ) :
      (Real.exp (-mu)*mu^n/n.factorial)*countedWordMass A B U n j s ≤
        poissonWordTerm mu a b j n*U s := by
    have h := mul_le_mul_of_nonneg_left
      (counted_word_majorant A B U a b hA hB ha hb hAU hBU n j s) (hp n)
    simpa only [poissonWordTerm,mul_assoc] using h
  have hmajor := (poisson_word_hasSum mu a b j).mul_right (U s)
  have hsum := Summable.of_nonneg_of_le hnonneg hle hmajor.summable
  exact hasSum_le hle hsum.hasSum hmajor

theorem counted_poisson_few_resets_bound {S : Type} [Fintype S]
    (A B : S → S → ℝ) (U : S → ℝ) (a b mu : ℝ)
    (hA : ∀ s t, 0 ≤ A s t) (hB : ∀ s t, 0 ≤ B s t)
    (hU : ∀ s, 0 ≤ U s) (ha : 0 ≤ a) (hb : 0 ≤ b) (hmu : 0 ≤ mu)
    (hAU : ∀ s, finiteRowApply A U s ≤ a*U s)
    (hBU : ∀ s, finiteRowApply B U s ≤ b*U s) (K : ℕ) (s : S) :
    (∑ j ∈ Finset.range K, countedPoissonMass A B U mu j s) ≤
      Real.exp (mu*(a-1))*(∑ j ∈ Finset.range K, (mu*b)^j/j.factorial)*U s := by
  have h := Finset.sum_le_sum (s := Finset.range K)
    (fun j _ => counted_poisson_bound A B U a b mu hA hB hU ha hb hmu hAU hBU j s)
  convert h using 1
  rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

end
end P161Formal

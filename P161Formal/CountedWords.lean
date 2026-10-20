module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-! Positive counted-word comparison for the recovery proof.
The two matrices are the non-reset and actual-reset marked subkernels.
Their witness inequalities remain explicit until the source bridge is proved;
this module supplies the combinatorial iteration, not a stochastic assumption.
-/

@[expose] public section
namespace P161Formal
open scoped BigOperators
noncomputable section

def binomialWordCoefficient (n j : ℕ) (a b : ℝ) : ℝ :=
  (n.choose j : ℝ) * a^(n-j) * b^j

theorem word_coefficient_nonnegative (n j : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ binomialWordCoefficient n j a b := by
  unfold binomialWordCoefficient
  positivity

theorem word_coefficient_zero (n : ℕ) (a b : ℝ) :
    binomialWordCoefficient (n+1) 0 a b = a * binomialWordCoefficient n 0 a b := by
  simp only [binomialWordCoefficient, Nat.choose_zero_right, Nat.cast_one,
    Nat.sub_zero, pow_zero, one_mul, mul_one, pow_succ]
  ring

theorem word_coefficient_pascal (n j : ℕ) (a b : ℝ) :
    binomialWordCoefficient (n+1) (j+1) a b =
      a * binomialWordCoefficient n (j+1) a b + b * binomialWordCoefficient n j a b := by
  by_cases hj : j < n
  · have he : n-j = (n-(j+1))+1 := by omega
    have ht : n+1-(j+1) = n-j := by omega
    simp only [binomialWordCoefficient, Nat.choose_succ_succ, Nat.cast_add, ht, he, pow_succ]
    ring
  · by_cases he : j = n
    · subst j
      simp [binomialWordCoefficient,pow_succ,mul_comm]
    · have hnj : n < j := by omega
      simp [binomialWordCoefficient,
        Nat.choose_eq_zero_of_lt hnj,
        Nat.choose_eq_zero_of_lt (show n < j+1 by omega),
        Nat.choose_eq_zero_of_lt (show n+1 < j+1 by omega)]

def finiteRowApply {S : Type} [Fintype S] (K : S → S → ℝ) (f : S → ℝ) (s : S) : ℝ :=
  ∑ t, K s t * f t

theorem positive_row_domination {S : Type} [Fintype S]
    (K : S → S → ℝ) (U f : S → ℝ) (c rate : ℝ)
    (hK : ∀ s t, 0 ≤ K s t) (hc : 0 ≤ c)
    (hf : ∀ t, f t ≤ c * U t)
    (hU : ∀ s, finiteRowApply K U s ≤ rate * U s) (s : S) :
    finiteRowApply K f s ≤ c * rate * U s := by
  have hs := Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hf t) (hK s t))
  have hid : (∑ t, K s t * (c * U t)) = c * finiteRowApply K U s := by
    rw [finiteRowApply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  change finiteRowApply K f s ≤ _ at hs
  rw [hid] at hs
  have h := mul_le_mul_of_nonneg_left (hU s) hc
  exact le_trans hs (by simpa only [mul_assoc] using h)

def countedWordMass {S : Type} [Fintype S] (A B : S → S → ℝ) (U : S → ℝ) :
    ℕ → ℕ → S → ℝ
  | 0, 0, s => U s
  | 0, _+1, _ => 0
  | n+1, 0, s => finiteRowApply A (countedWordMass A B U n 0) s
  | n+1, j+1, s => finiteRowApply A (countedWordMass A B U n (j+1)) s +
      finiteRowApply B (countedWordMass A B U n j) s

theorem counted_word_majorant {S : Type} [Fintype S]
    (A B : S → S → ℝ) (U : S → ℝ) (a b : ℝ)
    (hA : ∀ s t, 0 ≤ A s t) (hB : ∀ s t, 0 ≤ B s t)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hAU : ∀ s, finiteRowApply A U s ≤ a * U s)
    (hBU : ∀ s, finiteRowApply B U s ≤ b * U s)
    (n j : ℕ) (s : S) :
    countedWordMass A B U n j s ≤ binomialWordCoefficient n j a b * U s := by
  induction n generalizing j s with
  | zero => cases j <;> simp [countedWordMass, binomialWordCoefficient]
  | succ n ih =>
      cases j with
      | zero =>
          rw [countedWordMass, word_coefficient_zero]
          have h := positive_row_domination A U (countedWordMass A B U n 0)
            (binomialWordCoefficient n 0 a b) a hA (word_coefficient_nonnegative n 0 a b ha hb)
            (fun t => ih 0 t) hAU s
          simpa only [mul_comm a, mul_assoc] using h
      | succ j =>
          rw [countedWordMass]
          have h1 := positive_row_domination A U (countedWordMass A B U n (j+1))
            (binomialWordCoefficient n (j+1) a b) a hA
            (word_coefficient_nonnegative n (j+1) a b ha hb) (fun t => ih (j+1) t) hAU s
          have h2 := positive_row_domination B U (countedWordMass A B U n j)
            (binomialWordCoefficient n j a b) b hB
            (word_coefficient_nonnegative n j a b ha hb) (fun t => ih j t) hBU s
          calc
            _ ≤ binomialWordCoefficient n (j+1) a b * a * U s +
                binomialWordCoefficient n j a b * b * U s := add_le_add h1 h2
            _ = binomialWordCoefficient (n+1) (j+1) a b * U s := by
              rw [word_coefficient_pascal]
              ring

end
end P161Formal

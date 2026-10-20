module

public import P161Formal.MarkedSuboperators
public import P161Formal.CountedPoissonBound

/-! Counted-word comparison for positive suboperators on arbitrary raw states.
This removes the finite-state restriction from the existing matrix argument;
only source proposal marks need be finite. Physical-event docking is separate. -/

@[expose] public section
namespace P161Formal
open scoped BigOperators
noncomputable section

theorem submarkov_nonnegative {S : Type} (K : FunctionalCapacity.SubMarkov S)
    (f : S → ℝ) (hf : ∀ s, 0 ≤ f s) (s : S) : 0 ≤ K.P f s := by
  have hz : K.P (fun _ => 0) s = 0 := by
    simpa only [zero_mul] using K.smul 0 (fun _ => 0) s
  have h := K.mono (fun _ => 0) f hf s
  rwa [hz] at h

theorem submarkov_witness_domination {S : Type} (K : FunctionalCapacity.SubMarkov S)
    (U f : S → ℝ) (c rate : ℝ) (hc : 0 ≤ c)
    (hf : ∀ s, f s ≤ c*U s) (hKU : ∀ s, K.P U s ≤ rate*U s) (s : S) :
    K.P f s ≤ c*rate*U s := by
  have h := K.mono f (fun s => c*U s) hf s
  rw [K.smul] at h
  have hr := mul_le_mul_of_nonneg_left (hKU s) hc
  exact le_trans h (by simpa only [mul_assoc] using hr)

def submarkovWordMass {S : Type} (A B : FunctionalCapacity.SubMarkov S) (U : S → ℝ) :
    ℕ → ℕ → S → ℝ
  | 0, 0, s => U s
  | 0, _+1, _ => 0
  | n+1, 0, s => A.P (submarkovWordMass A B U n 0) s
  | n+1, j+1, s => A.P (submarkovWordMass A B U n (j+1)) s +
      B.P (submarkovWordMass A B U n j) s

theorem submarkov_word_nonnegative {S : Type} (A B : FunctionalCapacity.SubMarkov S)
    (U : S → ℝ) (hU : ∀ s, 0 ≤ U s) (n j : ℕ) (s : S) :
    0 ≤ submarkovWordMass A B U n j s := by
  induction n generalizing j s with
  | zero => cases j <;> simp [submarkovWordMass,hU]
  | succ n ih =>
      cases j with
      | zero => exact submarkov_nonnegative A _ (fun s => ih 0 s) s
      | succ j =>
          exact add_nonneg (submarkov_nonnegative A _ (fun s => ih (j+1) s) s)
            (submarkov_nonnegative B _ (fun s => ih j s) s)

theorem submarkov_counted_word_majorant {S : Type} (A B : FunctionalCapacity.SubMarkov S)
    (U : S → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hAU : ∀ s, A.P U s ≤ a*U s) (hBU : ∀ s, B.P U s ≤ b*U s)
    (n j : ℕ) (s : S) :
    submarkovWordMass A B U n j s ≤ binomialWordCoefficient n j a b*U s := by
  induction n generalizing j s with
  | zero => cases j <;> simp [submarkovWordMass,binomialWordCoefficient]
  | succ n ih =>
      cases j with
      | zero =>
          rw [submarkovWordMass,word_coefficient_zero]
          have h := submarkov_witness_domination A U (submarkovWordMass A B U n 0)
            (binomialWordCoefficient n 0 a b) a (word_coefficient_nonnegative n 0 a b ha hb)
            (fun s => ih 0 s) hAU s
          simpa only [mul_comm a,mul_assoc] using h
      | succ j =>
          rw [submarkovWordMass]
          have h1 := submarkov_witness_domination A U (submarkovWordMass A B U n (j+1))
            (binomialWordCoefficient n (j+1) a b) a
            (word_coefficient_nonnegative n (j+1) a b ha hb) (fun s => ih (j+1) s) hAU s
          have h2 := submarkov_witness_domination B U (submarkovWordMass A B U n j)
            (binomialWordCoefficient n j a b) b
            (word_coefficient_nonnegative n j a b ha hb) (fun s => ih j s) hBU s
          calc
            _ ≤ binomialWordCoefficient n (j+1) a b*a*U s +
                binomialWordCoefficient n j a b*b*U s := add_le_add h1 h2
            _ = binomialWordCoefficient (n+1) (j+1) a b*U s := by
              rw [word_coefficient_pascal]
              ring

def submarkovPoissonMass {S : Type} (A B : FunctionalCapacity.SubMarkov S)
    (U : S → ℝ) (mu : ℝ) (j : ℕ) (s : S) : ℝ :=
  ∑' n, (Real.exp (-mu)*mu^n/n.factorial)*submarkovWordMass A B U n j s

theorem submarkov_poisson_count_bound {S : Type} (A B : FunctionalCapacity.SubMarkov S)
    (U : S → ℝ) (a b mu : ℝ) (hU : ∀ s, 0 ≤ U s)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hmu : 0 ≤ mu)
    (hAU : ∀ s, A.P U s ≤ a*U s) (hBU : ∀ s, B.P U s ≤ b*U s) (j : ℕ) (s : S) :
    submarkovPoissonMass A B U mu j s ≤
      (Real.exp (mu*(a-1))*(mu*b)^j/j.factorial)*U s := by
  have hp (n : ℕ) : 0 ≤ Real.exp (-mu)*mu^n/n.factorial := by positivity
  have hnonneg (n : ℕ) :
      0 ≤ (Real.exp (-mu)*mu^n/n.factorial)*submarkovWordMass A B U n j s :=
    mul_nonneg (hp n) (submarkov_word_nonnegative A B U hU n j s)
  have hle (n : ℕ) :
      (Real.exp (-mu)*mu^n/n.factorial)*submarkovWordMass A B U n j s ≤
        poissonWordTerm mu a b j n*U s := by
    have h := mul_le_mul_of_nonneg_left
      (submarkov_counted_word_majorant A B U a b ha hb hAU hBU n j s) (hp n)
    simpa only [poissonWordTerm,mul_assoc] using h
  have hmajor := (poisson_word_hasSum mu a b j).mul_right (U s)
  have hsum := Summable.of_nonneg_of_le hnonneg hle hmajor.summable
  exact hasSum_le hle hsum.hasSum hmajor

end
end P161Formal

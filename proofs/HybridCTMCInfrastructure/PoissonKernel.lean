module

public import proofs.HybridCTMCInfrastructure.FiniteBounds
public import Mathlib.Probability.Distributions.Poisson.Basic

@[expose] public section

/-! A genuine probability distribution for the uniformization clock mixture.
The tail bound is proved from the generator's discrete kernel, not assumed.
Identification with a path-valued CTMC and its compensator is a separate obligation. -/
namespace HybridCTMC
open scoped BigOperators NNReal ENNReal
noncomputable section
variable {S : Type*} [Fintype S]

def mass (p : PMF S) (A : S → Prop) [DecidablePred A] : ℝ≥0∞ :=
  ∑' y, if A y then p y else 0

omit [Fintype S] in
theorem mass_bind {I : Type*} (p : PMF I) (K : I → PMF S)
    (A : S → Prop) [DecidablePred A] :
    mass (p.bind K) A = ∑' i, p i * mass (K i) A := by
  simp only [mass, PMF.bind_apply]
  calc
    (∑' y, if A y then ∑' i, p i * K i y else 0) =
        ∑' y, ∑' i, p i * (if A y then K i y else 0) := by
      apply tsum_congr
      intro y
      by_cases hy : A y <;> simp [hy]
    _ = ∑' i, ∑' y, p i * (if A y then K i y else 0) := ENNReal.tsum_comm
    _ = _ := by simp_rw [ENNReal.tsum_mul_left]

theorem mass_kernel (K : Kernel S) (A : S → Prop) [DecidablePred A] (x : S) :
    mass (K.pmf x) A = ENNReal.ofReal (K.event A x) := by
  rw [mass, tsum_fintype, K.event_eq_pmf]

def poissonWeight (r : ℝ≥0) (n : ℕ) : ℝ :=
  Real.exp (-(r : ℝ)) * (r : ℝ)^n / (n.factorial : ℝ)

theorem poissonWeight_nonneg (r : ℝ≥0) (n : ℕ) : 0 ≤ poissonWeight r n := by
  unfold poissonWeight
  positivity

theorem poisson_geometric_sum (r : ℝ≥0) (a : ℝ) :
    HasSum (fun n => poissonWeight r n * a^n) (Real.exp ((r : ℝ)*(a-1))) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ)*a)).mul_left
    (Real.exp (-(r : ℝ)))
  convert h using 1
  · funext n
    simp only [poissonWeight, mul_pow]
    ring
  · rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]
    congr 1
    ring

namespace Kernel
def poisson (K : Kernel S) (r : ℝ≥0) (x : S) : PMF S :=
  (ProbabilityTheory.poissonMeasure r).toPMF.bind (fun n => (K.power n).pmf x)

theorem poisson_event (K : Kernel S) (r : ℝ≥0)
    (A : S → Prop) [DecidablePred A] (x : S) :
    mass (K.poisson r x) A = ∑' n,
      ENNReal.ofReal (poissonWeight r n) * ENNReal.ofReal ((K.power n).event A x) := by
  rw [poisson, mass_bind]
  apply tsum_congr
  intro n
  rw [mass_kernel, MeasureTheory.Measure.toPMF_apply,
    ProbabilityTheory.poissonMeasure_singleton]
  rfl

/-- Affine residual-tail estimate after a Poisson number of transitions. -/
theorem poisson_tail (K : Kernel S) (r : ℝ≥0) (f : S → ℝ)
    (hf : ∀ x, 0 ≤ f x) {a B b : ℝ} (ha : 0 ≤ a) (hB : 0 ≤ B) (hb : 0 < b)
    (drift : ∀ x, K.expect f x ≤ a*f x+(1-a)*B)
    (A : S → Prop) [DecidablePred A] (barrier : ∀ x, A x → b ≤ f x) (x : S) :
    mass (K.poisson r x) A ≤
      ENNReal.ofReal ((Real.exp ((r : ℝ)*(a-1))*f x+B)/b) := by
  have hg := (poisson_geometric_sum r a).mul_right (f x)
  have hc := (ProbabilityTheory.hasSum_one_poissonMeasure r).mul_right B
  have hs : HasSum (fun n => poissonWeight r n * ((a^n*f x+B)/b))
      ((Real.exp ((r : ℝ)*(a-1))*f x+B)/b) := by
    convert (hg.add hc).div_const b using 1
    · funext n
      dsimp [poissonWeight]
      ring
    · ring
  rw [poisson_event]
  calc
    (∑' n, ENNReal.ofReal (poissonWeight r n)*ENNReal.ofReal ((K.power n).event A x)) ≤
        ∑' n, ENNReal.ofReal (poissonWeight r n * ((a^n*f x+B)/b)) := by
      apply ENNReal.tsum_le_tsum
      intro n
      rw [ENNReal.ofReal_mul (poissonWeight_nonneg r n)]
      apply mul_le_mul_right
      apply ENNReal.ofReal_le_ofReal
      calc
        (K.power n).event A x ≤ (K.power n).expect f x/b :=
          (K.power n).event_bound A f hf hb barrier x
        _ ≤ (a^n*f x+B)/b := by
          rw [power_expect]
          exact div_le_div_of_nonneg_right (K.iterate_affine f ha hB drift n x) hb.le
    _ = _ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg
        (poissonWeight_nonneg r n) (div_nonneg (add_nonneg
          (mul_nonneg (pow_nonneg ha n) (hf x)) hB) hb.le)) hs.summable, hs.tsum_eq]
end Kernel
end
end HybridCTMC

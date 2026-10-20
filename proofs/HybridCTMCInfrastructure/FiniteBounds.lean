module

public import proofs.HybridCTMCInfrastructure.FiniteKernel

@[expose] public section

namespace HybridCTMC
open scoped BigOperators
noncomputable section
variable {S : Type*} [Fintype S]
namespace Kernel

def identity : Kernel S := by
  classical
  exact ⟨fun x y => if y = x then 1 else 0,
    fun _ _ => by split_ifs <;> norm_num, fun _ => by simp⟩

def comp (K H : Kernel S) : Kernel S where
  weight x z := ∑ y, K.weight x y * H.weight y z
  nonneg x z := Finset.sum_nonneg fun y _ => mul_nonneg (K.nonneg x y) (H.nonneg y z)
  total x := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, H.total, mul_one]
    exact K.total x

theorem expect_identity (f : S → ℝ) (x : S) : identity.expect f x = f x := by
  classical
  simp [expect, identity]

theorem expect_comp (K H : Kernel S) (f : S → ℝ) (x : S) :
    (K.comp H).expect f x = K.expect (H.expect f) x := by
  simp only [expect, comp, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

def power (K : Kernel S) : ℕ → Kernel S
  | 0 => identity
  | n+1 => K.comp (K.power n)

theorem power_expect (K : Kernel S) (n : ℕ) (f : S → ℝ) (x : S) :
    (K.power n).expect f x = K.iterate n f x := by
  induction n generalizing x with
  | zero => exact expect_identity f x
  | succ n ih =>
    simp only [power, expect_comp, iterate]
    rw [funext ih]

theorem iterate_scale (K : Kernel S) (n : ℕ) (c : ℝ) (f : S → ℝ) (x : S) :
    K.iterate n (fun y => c*f y) x = c*K.iterate n f x := by
  rw [← power_expect, expect_scale, power_expect]

theorem iterate_add_const (K : Kernel S) (n : ℕ) (f : S → ℝ) (c : ℝ) (x : S) :
    K.iterate n (fun y => f y+c) x = K.iterate n f x+c := by
  rw [← power_expect, expect_add, expect_const, power_expect]

/-- Affine decay derived from one-step drift, without assuming a probability estimate. -/
theorem iterate_affine (K : Kernel S) (f : S → ℝ) {a B : ℝ} (ha : 0 ≤ a)
    (hB : 0 ≤ B) (h : ∀ x, K.expect f x ≤ a*f x+(1-a)*B)
    (n : ℕ) (x : S) : K.iterate n f x ≤ a^n*f x+B := by
  have hd : ∀ x, K.expect (fun y => f y + -B) x ≤ a*(f x + -B) := by
    intro y
    rw [expect_add, expect_const]
    nlinarith [h y]
  have hn := K.iterate_decay (fun y => f y + -B) ha hd n x
  rw [iterate_add_const] at hn
  nlinarith [mul_nonneg (pow_nonneg ha n) hB]

def event (K : Kernel S) (A : S → Prop) [DecidablePred A] (x : S) : ℝ :=
  K.expect (fun y => if A y then 1 else 0) x

/-- Finite Markov inequality; `event` is the sum of the event's probability masses. -/
theorem event_bound (K : Kernel S) (A : S → Prop) [DecidablePred A]
    (f : S → ℝ) (hf : ∀ x, 0 ≤ f x) {b : ℝ} (hb : 0 < b)
    (hA : ∀ x, A x → b ≤ f x) (x : S) : K.event A x ≤ K.expect f x/b := by
  have h := K.expect_mono (f := fun y => b*(if A y then 1 else 0)) (g := f)
    (fun y => by by_cases hy : A y; simpa [hy] using hA y hy; simpa [hy] using hf y) x
  rw [expect_scale] at h
  exact (le_div_iff₀ hb).mpr (by simpa [event, mul_comm] using h)

theorem event_eq_pmf (K : Kernel S) (A : S → Prop) [DecidablePred A] (x : S) :
    ENNReal.ofReal (K.event A x) = ∑ y, if A y then K.pmf x y else 0 := by
  rw [event, expect, ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro y _
    by_cases hy : A y <;> simp [hy, pmf, PMF.ofFintype_apply]
  · intro y _
    exact mul_nonneg (K.nonneg x y) (by split_ifs <;> norm_num)
end Kernel

namespace Rates
theorem stopped_rate_bound (q : Rates S) (safe : S → Prop) [DecidablePred safe]
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (h : ∀ x, ∑ y, q.rate x y ≤ Λ) (x : S) :
    ∑ y, (q.stopped safe).rate x y ≤ Λ := by
  by_cases hx : safe x
  · simpa [stopped, hx] using h x
  · simpa [stopped, hx] using hΛ

/-- Stopped finite-step exit estimate. Outside states are absorbing. Continuous-time
interpretation additionally requires the Poisson clock construction. -/
theorem stopped_exit_steps [DecidableEq S] (q : Rates S)
    (safe : S → Prop) [DecidablePred safe] (f : S → ℝ) (hf : ∀ x, 0 ≤ f x)
    {Λ c b : ℝ} (hΛ : 0 < Λ) (hc : 0 ≤ c) (hb : 0 < b)
    (bound : ∀ x, ∑ y, q.rate x y ≤ Λ)
    (drift : ∀ x, safe x → q.generator f x ≤ c)
    (barrier : ∀ x, ¬safe x → b ≤ f x) (n : ℕ) (x : S) :
    (((q.stopped safe).uniformize Λ hΛ (q.stopped_rate_bound safe hΛ.le bound)).power n).event
      (fun y => ¬safe y) x ≤ (f x+n*(c/Λ))/b := by
  let K := (q.stopped safe).uniformize Λ hΛ (q.stopped_rate_bound safe hΛ.le bound)
  have hstep : ∀ x, K.expect f x ≤ f x+c/Λ := by
    intro y
    rw [show K = _ from rfl, uniformize_expect]
    exact add_le_add_right (div_le_div_of_nonneg_right (q.stopped_drift safe f hc drift y) hΛ.le) _
  calc
    (K.power n).event (fun y => ¬safe y) x ≤ (K.power n).expect f x/b :=
      (K.power n).event_bound _ f hf hb barrier x
    _ ≤ (f x+n*(c/Λ))/b := by
      rw [Kernel.power_expect]
      exact div_le_div_of_nonneg_right (K.iterate_drift f (c/Λ) hstep n x) hb.le
end Rates
end
end HybridCTMC

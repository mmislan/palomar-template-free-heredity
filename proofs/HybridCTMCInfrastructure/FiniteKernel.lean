module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Measurability
public import Mathlib.Tactic.Finiteness
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Finite stochastic kernels and the uniformization step of a finite CTMC.
These results do not assert existence of a path-valued continuous-time process. -/
namespace HybridCTMC
open scoped BigOperators
noncomputable section
variable {S : Type*} [Fintype S]

structure Kernel (S : Type*) [Fintype S] where
  weight : S → S → ℝ
  nonneg : ∀ x y, 0 ≤ weight x y
  total : ∀ x, ∑ y, weight x y = 1

namespace Kernel
def expect (K : Kernel S) (f : S → ℝ) (x : S) : ℝ := ∑ y, K.weight x y * f y

theorem expect_mono (K : Kernel S) {f g : S → ℝ} (h : ∀ y, f y ≤ g y) (x : S) :
    K.expect f x ≤ K.expect g x :=
  Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (h y) (K.nonneg x y)

@[simp] theorem expect_const (K : Kernel S) (c : ℝ) (x : S) :
    K.expect (fun _ => c) x = c := by
  simp [expect, ← Finset.sum_mul, K.total]

theorem expect_add (K : Kernel S) (f g : S → ℝ) (x : S) :
    K.expect (fun y => f y + g y) x = K.expect f x + K.expect g x := by
  simp [expect, mul_add, Finset.sum_add_distrib]

theorem expect_scale (K : Kernel S) (c : ℝ) (f : S → ℝ) (x : S) :
    K.expect (fun y => c * f y) x = c * K.expect f x := by
  simp [expect, Finset.mul_sum]; congr 1; funext y; ring

def pmf (K : Kernel S) (x : S) : PMF S :=
  PMF.ofFintype (fun y => ENNReal.ofReal (K.weight x y)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => K.nonneg x y), K.total]
    simp)

def iterate (K : Kernel S) : ℕ → (S → ℝ) → S → ℝ
  | 0, f => f
  | n + 1, f => K.expect (K.iterate n f)

theorem iterate_mono (K : Kernel S) {f g : S → ℝ} (h : ∀ y, f y ≤ g y)
    (n : ℕ) (x : S) : K.iterate n f x ≤ K.iterate n g x := by
  induction n generalizing x with
  | zero => exact h x
  | succ n ih => exact K.expect_mono ih x

theorem iterate_drift (K : Kernel S) (f : S → ℝ) (c : ℝ)
    (h : ∀ x, K.expect f x ≤ f x + c) (n : ℕ) (x : S) :
    K.iterate n f x ≤ f x + n * c := by
  induction n generalizing x with
  | zero => simp [iterate]
  | succ n ih =>
    calc
      K.iterate (n+1) f x ≤ K.expect (fun y => f y + n*c) x := K.expect_mono ih x
      _ = K.expect f x + n*c := by rw [expect_add, expect_const]
      _ ≤ f x + (↑(n+1) : ℝ)*c := by push_cast; nlinarith [h x]

theorem iterate_decay (K : Kernel S) (f : S → ℝ) {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ x, K.expect f x ≤ a*f x) (n : ℕ) (x : S) :
    K.iterate n f x ≤ a^n*f x := by
  induction n generalizing x with
  | zero => simp [iterate]
  | succ n ih =>
    calc
      K.iterate (n+1) f x ≤ K.expect (fun y => a^n*f y) x := K.expect_mono ih x
      _ = a^n*K.expect f x := K.expect_scale _ _ _
      _ ≤ a^n*(a*f x) := mul_le_mul_of_nonneg_left (h x) (pow_nonneg ha n)
      _ = a^(n+1)*f x := by rw [pow_succ]; ring
end Kernel

structure Rates (S : Type*) [Fintype S] where
  rate : S → S → ℝ
  nonneg : ∀ x y, 0 ≤ rate x y

namespace Rates
def generator (q : Rates S) (f : S → ℝ) (x : S) : ℝ :=
  ∑ y, q.rate x y * (f y - f x)

def uniformize [DecidableEq S] (q : Rates S) (Λ : ℝ) (hΛ : 0 < Λ)
    (bound : ∀ x, ∑ y, q.rate x y ≤ Λ) : Kernel S where
  weight x y := (if y = x then 1 - (∑ z, q.rate x z)/Λ else 0) + q.rate x y/Λ
  nonneg x y := add_nonneg (by split_ifs; exact sub_nonneg.mpr ((div_le_one hΛ).mpr (bound x)); rfl)
    (div_nonneg (q.nonneg x y) hΛ.le)
  total x := by
    simp [Finset.sum_add_distrib, ← Finset.sum_div]

theorem uniformize_expect [DecidableEq S] (q : Rates S) (Λ : ℝ) (hΛ : 0 < Λ)
    (bound : ∀ x, ∑ y, q.rate x y ≤ Λ) (f : S → ℝ) (x : S) :
    (q.uniformize Λ hΛ bound).expect f x = f x + q.generator f x / Λ := by
  simp only [Kernel.expect, uniformize, add_mul, Finset.sum_add_distrib]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [generator, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  ring

/-- Killing sets the observable to zero outside the region. Nonnegative boundary values
make its generator no larger than the original generator at an interior state. -/
theorem killed_generator_le (q : Rates S) (safe : S → Prop) [DecidablePred safe]
    (f : S → ℝ) (hf : ∀ x, 0 ≤ f x) (x : S) (hx : safe x) :
    q.generator (fun y => if safe y then f y else 0) x ≤ q.generator f x := by
  apply Finset.sum_le_sum
  intro y _
  apply mul_le_mul_of_nonneg_left _ (q.nonneg x y)
  simp only [ite_eq_left hx]
  split_ifs <;> linarith [hf y]

def stopped (q : Rates S) (safe : S → Prop) [DecidablePred safe] : Rates S where
  rate x y := if safe x then q.rate x y else 0
  nonneg x y := by split_ifs; exact q.nonneg x y; rfl

theorem stopped_drift (q : Rates S) (safe : S → Prop) [DecidablePred safe]
    (f : S → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x, safe x → q.generator f x ≤ c) (x : S) :
    (q.stopped safe).generator f x ≤ c := by
  by_cases hx : safe x
  · simpa [generator, stopped, hx] using h x hx
  · simpa [generator, stopped, hx] using hc
end Rates
end
end HybridCTMC

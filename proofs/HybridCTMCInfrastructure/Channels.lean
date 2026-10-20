module

public import proofs.HybridCTMCInfrastructure.FiniteKernel

@[expose] public section

/-! Channel-indexed rate assembly retains reaction-correlated jumps. No independent
species-noise assumption is made. The squared-jump identity is generator algebra,
not yet a theorem about predictable quadratic variation. -/
namespace HybridCTMC
open scoped BigOperators
noncomputable section
variable {S R : Type*} [Fintype S] [Fintype R]

structure Channels (S R : Type*) where
  next : S → R → S
  propensity : S → R → ℝ
  nonneg : ∀ x r, 0 ≤ propensity x r

namespace Channels
def rates [DecidableEq S] (C : Channels S R) : Rates S where
  rate x y := ∑ r, if C.next x r = y then C.propensity x r else 0
  nonneg x y := Finset.sum_nonneg fun r _ => by split_ifs; exact C.nonneg x r; rfl

theorem total_rate [DecidableEq S] (C : Channels S R) (x : S) :
    ∑ y, C.rates.rate x y = ∑ r, C.propensity x r := by
  simp only [rates]
  rw [Finset.sum_comm]
  simp

theorem generator_eq [DecidableEq S] (C : Channels S R) (f : S → ℝ) (x : S) :
    C.rates.generator f x = ∑ r, C.propensity x r * (f (C.next x r)-f x) := by
  simp only [Rates.generator, rates, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  simp [ite_mul]

theorem square_generator [DecidableEq S] (C : Channels S R) (f : S → ℝ) (x : S) :
    C.rates.generator (fun y => (f y)^2) x - 2*f x*C.rates.generator f x =
      ∑ r, C.propensity x r * (f (C.next x r)-f x)^2 := by
  rw [generator_eq, generator_eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  ring

omit [Fintype S] in
/-- This is the source's concentration squared-jump-rate bound. A compensated
martingale theorem is still required to turn it into quadratic variation. -/
theorem square_rate_bound (C : Channels S R) (f : S → ℝ) (x : S)
    {J Rmax : ℝ} (hJ : 0 ≤ J)
    (jump : ∀ r, (f (C.next x r)-f x)^2 ≤ J)
    (total : ∑ r, C.propensity x r ≤ Rmax) :
    ∑ r, C.propensity x r*(f (C.next x r)-f x)^2 ≤ Rmax*J := by
  calc
    _ ≤ ∑ r, C.propensity x r*J := Finset.sum_le_sum fun r _ =>
      mul_le_mul_of_nonneg_left (jump r) (C.nonneg x r)
    _ = (∑ r, C.propensity x r)*J := (Finset.sum_mul ..).symm
    _ ≤ Rmax*J := mul_le_mul_of_nonneg_right total hJ
end Channels

/-- Distinct-reactant mass action, exactly Omega*k*product(n_i/Omega).
Repeated reactants need falling factorials and are outside this definition. -/
def massAction {d : ℕ} (reactants : Finset (Fin d)) (k Ω : ℝ)
    (n : Fin d → ℕ) : ℝ := Ω*k*∏ i ∈ reactants, ((n i : ℝ)/Ω)

theorem massAction_nonneg {d : ℕ} (reactants : Finset (Fin d)) {k Ω : ℝ}
    (hk : 0 ≤ k) (hΩ : 0 ≤ Ω) (n : Fin d → ℕ) : 0 ≤ massAction reactants k Ω n := by
  apply mul_nonneg (mul_nonneg hΩ hk)
  exact Finset.prod_nonneg fun i _ => div_nonneg (Nat.cast_nonneg _) hΩ

theorem massAction_disabled {d : ℕ} (reactants : Finset (Fin d)) (k Ω : ℝ)
    (n : Fin d → ℕ) (i : Fin d) (hi : i ∈ reactants) (hn : n i = 0) :
    massAction reactants k Ω n = 0 := by
  unfold massAction
  have hp : ∏ j ∈ reactants, ((n j : ℝ)/Ω) = 0 :=
    Finset.prod_eq_zero hi (by simp [hn])
  rw [hp, mul_zero]
end
end HybridCTMC

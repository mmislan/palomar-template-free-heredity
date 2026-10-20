module

public import proofs.HybridCTMCInfrastructure.PoissonKernel

@[expose] public section

/-! Conditional composition for actual probability kernels. Independence is not
required. Applying this to source operations still requires each source-specific
good-region bound; this theorem does not supply those estimates. -/
namespace HybridCTMC
open scoped ENNReal
noncomputable section
variable {S T : Type*}

theorem mass_le_one (p : PMF S) (A : S → Prop) [DecidablePred A] : mass p A ≤ 1 := by
  rw [← p.tsum_coe]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : A x <;> simp [hx]

theorem conditional_failure (p : PMF S) (K : S → PMF T)
    (ready : S → Prop) [DecidablePred ready] (bad : T → Prop) [DecidablePred bad]
    {ε δ : ℝ≥0∞} (initial : mass p (fun x => ¬ready x) ≤ ε)
    (uniform : ∀ x, ready x → mass (K x) bad ≤ δ) :
    mass (p.bind K) bad ≤ δ+ε := by
  rw [mass_bind]
  calc
    (∑' x, p x*mass (K x) bad) ≤
        ∑' x, p x*(δ+(if ¬ready x then 1 else 0)) := by
      apply ENNReal.tsum_le_tsum
      intro x
      apply mul_le_mul_right
      by_cases hx : ready x
      · simpa [hx] using uniform x hx
      · simp only [hx, not_false_eq_true, ite_true]
        exact (mass_le_one (K x) bad).trans (le_add_left le_rfl)
    _ = δ+mass p (fun x => ¬ready x) := by
      simp_rw [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, p.tsum_coe, one_mul]
      congr 1
      apply tsum_congr
      intro x
      by_cases hx : ready x <;> simp [hx]
    _ ≤ δ+ε := add_le_add_right initial δ
end
end HybridCTMC

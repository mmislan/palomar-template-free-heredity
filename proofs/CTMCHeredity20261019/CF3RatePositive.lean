module

public import proofs.FunctionalCapacity.Defs

@[expose] public section

/-!
# Minimal positivity of the literal CF3 marked-rate envelope

Source provenance: the algebra is extracted from
`E:/Erdos Problems/proofs/FunctionalCapacity/Mission.lean`, theorem
`FunctionalCapacity.cf3Rate_pos`, read-only SHA256
`6FFE47A1FCCBC5963BB1B2BA237AB3DB58548E196055A8C8D3264EE961D715A8`.

The original proof uses only a positive site count, nonnegative alpha/beta/seed
coefficients, and nonnegativity of natural counts. These primitive hypotheses
replace its enclosing `Par.Valid` package so this helper imports only `Defs`.
No mission, killed kernel, certificate, or historical root is imported.
-/

namespace CTMCHeredity20261019.CF3RatePositive

open FunctionalCapacity

/-- The unchanged source rate formula is positive whenever the site count is
positive and its physical coefficients are nonnegative. -/
theorem rate_pos {p : Par} (hM : 0 < p.M) (hα : 0 ≤ p.α)
    (hβ : 0 ≤ p.β) (hε : 0 ≤ p.ε) : 0 < cf3Rate p := by
  unfold cf3Rate
  have hMR : (0 : ℝ) < p.M := by exact_mod_cast hM
  have hc : (0 : ℝ) ≤ p.c := Nat.cast_nonneg _
  have hN : (0 : ℝ) ≤ p.N := Nat.cast_nonneg _
  have h1 : 0 ≤ (p.c : ℝ) *
      (p.ε + p.α * p.N + p.α / 2 * p.N + p.N + p.β) := by
    apply mul_nonneg hc
    have := mul_nonneg hα hN
    nlinarith
  apply mul_pos hMR
  linarith

end CTMCHeredity20261019.CF3RatePositive

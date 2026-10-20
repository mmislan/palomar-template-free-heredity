module

public import proofs.FunctionalCapacity.Defs
public import proofs.HybridCTMCInfrastructure.FiniteKernel

@[expose] public section

/-!
# Finite positive generators have actual stochastic uniformizations

This adapter reconstructs a finite-state kernel from `FunctionalCapacity.IsGen`.
Its transition weights are obtained from the generator on delta functions;
positivity and normalization are proved, rather than assumed.  It supplies the
operator input to the existing exponential-clock path construction.  This file
does not assert a deterministic-time Markov property or any path-law identity.
-/

namespace CTMCHeredity20261019

open scoped BigOperators
noncomputable section

variable {S : Type} [Fintype S] [DecidableEq S]
variable {L Lam : ℝ} {G : (S → ℝ) → S → ℝ}

/-- The real delta observable at a state. -/
def delta (y x : S) : ℝ := if y = x then 1 else 0

omit [Fintype S] in
theorem delta_nonneg (y x : S) : 0 ≤ delta y x := by
  unfold delta
  split_ifs <;> norm_num

theorem delta_sum (x : S) : (∑ y, delta y x) = 1 := by
  simp [delta]

theorem delta_basis (f : S → ℝ) (x : S) :
    (∑ y, f y * delta y x) = f x := by
  simp [delta, mul_ite]

omit [Fintype S] [DecidableEq S] in
theorem generator_zero (hG : FunctionalCapacity.IsGen L G) (x : S) :
    G (fun _ => 0) x = 0 := by
  have h := hG.smul 0 (fun _ => 1) x
  simpa using h

omit [Fintype S] [DecidableEq S] in
/-- Finite linearity is derived from the two primitive linearity fields. -/
theorem generator_sum {I : Type*} (hG : FunctionalCapacity.IsGen L G)
    (s : Finset I) (F : I → S → ℝ) (x : S) :
    G (fun z => ∑ i ∈ s, F i z) x = ∑ i ∈ s, G (F i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using generator_zero hG x
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [hG.add, ih]

/-- Reconstruct a finite generator from its values on the delta basis. -/
theorem generator_delta_basis (hG : FunctionalCapacity.IsGen L G)
    (f : S → ℝ) (x : S) :
    G f x = ∑ y, f y * G (delta y) x := by
  have hb : f = fun z => ∑ y, f y * delta y z := by
    funext z
    exact (delta_basis f z).symm
  calc
    G f x = G (fun z => ∑ y, f y * delta y z) x := congrArg (fun g => G g x) hb
    _ = ∑ y, G (fun z => f y * delta y z) x := by
      simpa using generator_sum hG Finset.univ (fun y z => f y * delta y z) x
    _ = ∑ y, f y * G (delta y) x := by
      apply Finset.sum_congr rfl
      intro y _
      exact hG.smul (f y) (delta y) x

/-- The actual stochastic kernel with expectation `f + G f / Lam`. -/
def uniformizedKernel (hG : FunctionalCapacity.IsGen L G)
    (hLam : 0 < Lam) (hL : L ≤ Lam) : HybridCTMC.Kernel S where
  weight x y := delta y x + G (delta y) x / Lam
  nonneg x y := by
    have hp := hG.pos (delta y) (delta_nonneg y) x
    have hm := mul_le_mul_of_nonneg_right hL (delta_nonneg y x)
    have hn : 0 ≤ Lam * delta y x + G (delta y) x := by linarith
    have he : delta y x + G (delta y) x / Lam =
        (Lam * delta y x + G (delta y) x) / Lam := by
      field_simp [hLam.ne']
    rw [he]
    exact div_nonneg hn hLam.le
  total x := by
    rw [Finset.sum_add_distrib, ← Finset.sum_div]
    have hg : (∑ y, G (delta y) x) = G (fun _ => 1) x := by
      have h := generator_sum hG Finset.univ delta x
      have hs : (fun z : S => ∑ y : S, delta y z) = (fun _ => (1 : ℝ)) := by
        funext z
        exact delta_sum z
      simpa only [hs] using h.symm
    rw [delta_sum, hg, hG.one]
    simp

theorem uniformizedKernel_expect (hG : FunctionalCapacity.IsGen L G)
    (hLam : 0 < Lam) (hL : L ≤ Lam) (f : S → ℝ) (x : S) :
    (uniformizedKernel hG hLam hL).expect f x = f x + G f x / Lam := by
  change (∑ y, (delta y x + G (delta y) x / Lam) * f y) = _
  calc
    _ = (∑ y, delta y x * f y) + (∑ y, f y * G (delta y) x) / Lam := by
      simp only [add_mul, Finset.sum_add_distrib]
      rw [Finset.sum_div]
      congr 1
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = f x + G f x / Lam := by
      rw [← generator_delta_basis hG f x]
      simp [delta, ite_mul]

theorem kernel_expect_delta (K : HybridCTMC.Kernel S) (x y : S) :
    K.expect (delta y) x = K.weight x y := by
  simp [HybridCTMC.Kernel.expect, delta, mul_ite]

/-- Equality of all expectations determines a finite stochastic kernel. -/
theorem kernel_eq_of_expect_eq (K H : HybridCTMC.Kernel S)
    (h : ∀ (f : S → ℝ) (x : S), K.expect f x = H.expect f x) : K = H := by
  have hw : K.weight = H.weight := by
    funext x y
    simpa only [kernel_expect_delta] using h (delta y) x
  cases K
  cases H
  cases hw
  rfl

/-- The adapter agrees with the existing rate-matrix uniformization whenever
the same generator has already been presented by nonnegative transition rates. -/
theorem uniformizedKernel_eq_rates_uniformize (q : HybridCTMC.Rates S)
    (hG : FunctionalCapacity.IsGen L q.generator)
    (hLam : 0 < Lam) (hL : L ≤ Lam)
    (bound : ∀ x, ∑ y, q.rate x y ≤ Lam) :
    uniformizedKernel hG hLam hL = q.uniformize Lam hLam bound := by
  apply kernel_eq_of_expect_eq
  intro f x
  rw [uniformizedKernel_expect, HybridCTMC.Rates.uniformize_expect]

/-- Indicator of the complement of a proposed invariant set. -/
def outsideIndicator (safe : S → Prop) [DecidablePred safe] (y : S) : ℝ :=
  if safe y then 0 else 1

omit [Fintype S] [DecidableEq S] in
theorem outsideIndicator_nonneg (safe : S → Prop) [DecidablePred safe] (y : S) :
    0 ≤ outsideIndicator safe y := by
  unfold outsideIndicator
  split_ifs <;> norm_num

/-- A zero generator on the complement indicator prevents every one-step
transition out of `safe`; no invariant-support hypothesis is assumed. -/
theorem uniformizedKernel_weight_eq_zero_of_invariant
    (hG : FunctionalCapacity.IsGen L G) (hLam : 0 < Lam) (hL : L ≤ Lam)
    (safe : S → Prop) [DecidablePred safe] (x : S) (hx : safe x)
    (hinv : G (outsideIndicator safe) x = 0) (y : S) (hy : ¬ safe y) :
    (uniformizedKernel hG hLam hL).weight x y = 0 := by
  let K := uniformizedKernel hG hLam hL
  have hz : K.expect (outsideIndicator safe) x = 0 := by
    rw [uniformizedKernel_expect, hinv]
    simp [outsideIndicator, hx]
  apply le_antisymm _ (K.nonneg x y)
  calc
    K.weight x y = K.weight x y * outsideIndicator safe y := by
      simp [outsideIndicator, hy]
    _ ≤ ∑ z, K.weight x z * outsideIndicator safe z :=
      Finset.single_le_sum (fun z _ =>
        mul_nonneg (K.nonneg x z) (outsideIndicator_nonneg safe z)) (Finset.mem_univ y)
    _ = 0 := hz

/-- The constructed probability distribution stays in an invariant set. -/
theorem uniformizedKernel_support_safe
    (hG : FunctionalCapacity.IsGen L G) (hLam : 0 < Lam) (hL : L ≤ Lam)
    (safe : S → Prop) [DecidablePred safe]
    (hinv : ∀ x, safe x → G (outsideIndicator safe) x = 0)
    (x : S) (hx : safe x) :
    ((uniformizedKernel hG hLam hL).pmf x).support ⊆ {y | safe y} := by
  intro y hy
  by_contra hn
  have hw := uniformizedKernel_weight_eq_zero_of_invariant hG hLam hL safe x hx
    (hinv x hx) y hn
  have hp : (uniformizedKernel hG hLam hL).pmf x y = 0 := by
    simp [HybridCTMC.Kernel.pmf, PMF.ofFintype_apply, hw]
  exact (((uniformizedKernel hG hLam hL).pmf x).mem_support_iff y).mp hy hp

end
end CTMCHeredity20261019

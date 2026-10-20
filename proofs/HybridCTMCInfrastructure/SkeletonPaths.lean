module

public import proofs.HybridCTMCInfrastructure.PoissonExit
public import proofs.HybridCTMCInfrastructure.Composition

@[expose] public section

/-! Finite path laws for the uniformized jump skeleton, including its initial
state. Poisson mixing gives random finite histories. This is not yet a cadlag
process with a filtration and compensated time integrals. -/
namespace HybridCTMC
open scoped BigOperators NNReal ENNReal Classical
noncomputable section
variable {S : Type*} [Fintype S]

omit [Fintype S] in
theorem mass_pure (x : S) (A : S → Prop) [DecidablePred A] :
    mass (PMF.pure x) A = if A x then 1 else 0 := by
  simp only [mass, PMF.pure_apply]
  have he : (fun y => if A y then (if y=x then (1:ℝ≥0∞) else 0) else 0) =
      (fun y => if y=x then (if A x then 1 else 0) else 0) := by
    funext y
    by_cases hy : y=x <;> simp [hy]
  rw [he, tsum_ite_eq]

omit [Fintype S] in
theorem mass_map {T : Type*} (p : PMF S) (f : S → T) (A : T → Prop) [DecidablePred A] :
    mass (p.map f) A = mass p (fun x => A (f x)) := by
  rw [PMF.map, mass_bind]
  simp only [Function.comp_apply, mass_pure]
  apply tsum_congr
  intro x
  by_cases hx : A (f x) <;> simp [hx]

namespace Kernel
theorem comp_pmf (K H : Kernel S) (x : S) :
    (K.comp H).pmf x = (K.pmf x).bind (fun y => H.pmf y) := by
  apply PMF.ext
  intro z
  simp only [pmf, PMF.ofFintype_apply, comp, PMF.bind_apply, tsum_fintype]
  rw [ENNReal.ofReal_sum_of_nonneg (fun y _ => mul_nonneg (K.nonneg x y) (H.nonneg y z))]
  apply Finset.sum_congr rfl
  intro y _
  exact ENNReal.ofReal_mul (K.nonneg x y)

theorem identity_pmf (x : S) : (identity : Kernel S).pmf x = PMF.pure x := by
  apply PMF.ext
  intro y
  by_cases hy : y=x <;> simp [pmf, identity, PMF.pure_apply, hy]

def stop (K : Kernel S) (safe : S → Prop) [DecidablePred safe] : Kernel S where
  weight x y := if safe x then K.weight x y else identity.weight x y
  nonneg x y := by split_ifs; exact K.nonneg x y; exact identity.nonneg x y
  total x := by
    by_cases hx : safe x <;> simp only [hx, ite_true, ite_false]
    · exact K.total x
    · exact identity.total x

theorem stop_pmf (K : Kernel S) (safe : S → Prop) [DecidablePred safe] (x : S) :
    (K.stop safe).pmf x = if safe x then K.pmf x else PMF.pure x := by
  by_cases hx : safe x
  · apply PMF.ext
    intro y
    simp [pmf, stop, hx]
  · rw [ite_eq_right hx, ← identity_pmf]
    apply PMF.ext
    intro y
    simp [pmf, stop, hx]

def trajectory (K : Kernel S) : ℕ → S → PMF (List S)
  | 0, x => PMF.pure [x]
  | n+1, x => (K.pmf x).bind (fun y => (K.trajectory n y).map (List.cons x))

def exited (safe : S → Prop) (xs : List S) : Prop := ∃ x ∈ xs, ¬safe x

instance (safe : S → Prop) [DecidablePred safe] (xs : List S) : Decidable (exited safe xs) :=
  inferInstanceAs (Decidable (∃ x ∈ xs, ¬safe x))

theorem trajectory_outside (K : Kernel S) (safe : S → Prop) [DecidablePred safe]
    (n : ℕ) (x : S) (hx : ¬safe x) : mass (K.trajectory n x) (exited safe) = 1 := by
  cases n with
  | zero => simp [trajectory, mass_pure, exited, hx]
  | succ n =>
    rw [trajectory, mass_bind]
    have he : (fun xs : List S => exited safe (x::xs)) = fun _ => True := by
      funext xs
      simp [exited, hx]
    simp_rw [mass_map, he]
    simp only [mass, ite_true, PMF.tsum_coe, mul_one]

/-- Ever exiting along the original finite path equals being outside at the end
of the stopped chain. This supplies the missing finite-skeleton exit meaning. -/
theorem trajectory_exit (K : Kernel S) (safe : S → Prop) [DecidablePred safe]
    (n : ℕ) (x : S) :
    mass (K.trajectory n x) (exited safe) =
      mass (((K.stop safe).power n).pmf x) (fun y => ¬safe y) := by
  induction n generalizing x with
  | zero => simp [trajectory, power, identity_pmf, mass_pure, exited]
  | succ n ih =>
    by_cases hx : safe x
    · rw [trajectory, mass_bind, power, comp_pmf, mass_bind, stop_pmf, ite_eq_left hx]
      apply tsum_congr
      intro y
      rw [mass_map]
      have he : (fun xs : List S => exited safe (x::xs)) = exited safe := by
        funext xs
        simp [exited, hx]
      simp only [he, ih]
    · rw [trajectory_outside K safe (n+1) x hx, power, comp_pmf, stop_pmf,
        ite_eq_right hx, PMF.pure_bind]
      rw [← ih]
      exact (trajectory_outside K safe n x hx).symm

def poissonTrajectory (K : Kernel S) (r : ℝ≥0) (x : S) : PMF (List S) :=
  (ProbabilityTheory.poissonMeasure r).toPMF.bind (fun n => K.trajectory n x)

theorem poissonTrajectory_exit (K : Kernel S) (safe : S → Prop) [DecidablePred safe]
    (r : ℝ≥0) (x : S) :
    mass (K.poissonTrajectory r x) (exited safe) =
      mass ((K.stop safe).poisson r x) (fun y => ¬safe y) := by
  rw [poissonTrajectory, poisson, mass_bind, mass_bind]
  apply tsum_congr
  intro n
  rw [trajectory_exit]
end Kernel
end
end HybridCTMC

module

public import proofs.CTMCHeredity20261019.MissionQuotient
public import proofs.HybridCTMCInfrastructure.SurvivalCoupling

@[expose] public section

/-!
# Source killed CT operators are actual no-exit endpoint expectations

The actual single-horizon history theorem in `SurvivalCoupling` is reused.
Only the finite killed-iteration and real/ENNReal series glue is proved here.
There is no path-law premise. The zero-tick convention is explicit: the
unrestricted theorem requires the endpoint reward to vanish on dead states;
the usual theorem instead requires a safe initial state. This does not alter
the original source operator or its mission definitions.
-/

namespace CTMCHeredity20261019

open FunctionalCapacity MeasureTheory HybridCTMC
open scoped BigOperators NNReal ENNReal Classical
noncomputable section

section SubMarkovBounds

variable {A : Type}

private theorem sourceP_zero (Q : SubMarkov A) (x : A) :
    Q.P (fun _ => 0) x = 0 := by
  simpa using Q.smul 0 (fun _ => 0) x

private theorem sourceIter_succ_left (Q : SubMarkov A) (n : ℕ)
    (f : A → ℝ) (x : A) :
    Q.iter (n + 1) f x = Q.P (Q.iter n f) x := by
  induction n generalizing f x with
  | zero => rfl
  | succ n ih =>
      change Q.iter (n + 1) (Q.P f) x = Q.P (Q.iter (n + 1) f) x
      rw [ih]
      rfl

private theorem sourceIter_nonneg (Q : SubMarkov A) {f : A → ℝ}
    (hf : ∀ x, 0 ≤ f x) (n : ℕ) (x : A) : 0 ≤ Q.iter n f x := by
  induction n generalizing x with
  | zero => exact hf x
  | succ n ih =>
      rw [sourceIter_succ_left]
      calc
        0 = Q.P (fun _ => 0) x := (sourceP_zero Q x).symm
        _ ≤ Q.P (Q.iter n f) x := Q.mono _ _ ih x

private theorem sourceP_const_le (Q : SubMarkov A) {B : ℝ}
    (hB : 0 ≤ B) (x : A) : Q.P (fun _ => B) x ≤ B := by
  have h := Q.smul B (fun _ => 1) x
  simp only [mul_one] at h
  rw [h]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (Q.le_one x) hB

private theorem sourceIter_le (Q : SubMarkov A) {f : A → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hf : ∀ x, f x ≤ B) (n : ℕ) (x : A) :
    Q.iter n f x ≤ B := by
  induction n generalizing x with
  | zero => exact hf x
  | succ n ih =>
      rw [sourceIter_succ_left]
      exact (Q.mono _ _ ih x).trans (sourceP_const_le Q hB x)

private theorem sourcePois_nonneg {μ : ℝ} (hμ : 0 ≤ μ) (n : ℕ) :
    0 ≤ pois μ n := by
  unfold pois
  positivity

/-- Finite-state nonnegative rewards make the source real series summable.
This elementary bound avoids importing the rest of the source certificate calculus. -/
private theorem sourceCT_summable [Fintype A] (Q : SubMarkov A)
    {f : A → ℝ} (hf : ∀ x, 0 ≤ f x) {μ : ℝ} (hμ : 0 ≤ μ) (x : A) :
    Summable (fun n => pois μ n * Q.iter n f x) := by
  let B : ℝ := ∑ y, f y
  have hB : 0 ≤ B := Finset.sum_nonneg (fun y _ => hf y)
  have hfB (y : A) : f y ≤ B :=
    Finset.single_le_sum (fun z _ => hf z) (Finset.mem_univ y)
  have hp : Summable (fun n => pois μ n) := by
    convert (ProbabilityTheory.hasSum_one_poissonMeasure (⟨μ, hμ⟩ : ℝ≥0)).summable using 1
    funext n
    change Real.exp (-μ) * (μ ^ n / (n.factorial : ℝ)) =
      Real.exp (-μ) * μ ^ n / (n.factorial : ℝ)
    ring
  refine Summable.of_norm_bounded (g := fun n => |pois μ n| * B)
    (hp.abs.mul_right B) ?_
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sourceIter_nonneg Q hf n x)]
  exact mul_le_mul_of_nonneg_left (sourceIter_le Q hB hfB n x) (abs_nonneg _)

end SubMarkovBounds

section FiniteHistories

variable {S : Type} [Fintype S]

private theorem nnReward_congr_support {I : Type*} (p : PMF I)
    (f g : I → ℝ≥0∞) (h : ∀ i ∈ p.support, f i = g i) :
    nnReward p f = nnReward p g := by
  unfold nnReward
  apply tsum_congr
  intro i
  by_cases hi : p i = 0
  · simp [hi]
  · rw [h i (by simpa only [PMF.mem_support_iff] using hi)]

/-- Finite-kernel instance of the existing nonnegative reward sum. This is
the elementary `Moments.reward_kernel` calculation without importing its DAG. -/
private theorem nnReward_kernel_ofReal (K : HybridCTMC.Kernel S)
    (f : S → ℝ) (hf : ∀ y, 0 ≤ f y) (x : S) :
    nnReward (K.pmf x) (fun y => ENNReal.ofReal (f y)) =
      ENNReal.ofReal (K.expect f x) := by
  rw [nnReward, tsum_fintype, HybridCTMC.Kernel.expect,
    ENNReal.ofReal_sum_of_nonneg
      (fun y _ => mul_nonneg (K.nonneg x y) (hf y))]
  apply Finset.sum_congr rfl
  intro y _
  simp only [HybridCTMC.Kernel.pmf, PMF.ofFintype_apply]
  exact (ENNReal.ofReal_mul (K.nonneg x y)).symm

private theorem sourceIter_dead_zero (K : HybridCTMC.Kernel S) (Q : SubMarkov S)
    (dead : S → Prop)
    (hstep : ∀ f x, Q.P f x = if dead x then 0 else K.expect (kill dead f) x)
    {f : S → ℝ} (hf : ∀ x, dead x → f x = 0)
    (n : ℕ) (x : S) (hx : dead x) : Q.iter n f x = 0 := by
  cases n with
  | zero => exact hf x hx
  | succ n => rw [sourceIter_succ_left, hstep]; simp [hx]

/-- The finite visited-history calculation. The one-step identity will be
discharged by `stepK_as_stochastic_kernel` in the source-facing theorem. -/
private theorem trajectory_surviving_endpoint (K : HybridCTMC.Kernel S)
    (Q : SubMarkov S) (dead : S → Prop)
    (hstep : ∀ f x, Q.P f x = if dead x then 0 else K.expect (kill dead f) x)
    (f : S → ℝ) (hf : ∀ x, 0 ≤ f x) (hdead : ∀ x, dead x → f x = 0)
    (n : ℕ) (x : S) :
    nnReward (K.trajectory n x)
      (HybridCTMC.Kernel.survivingReward (fun y => ¬ dead y)
        (fun xs => ENNReal.ofReal (f (xs.getLastD x)))) =
      ENNReal.ofReal (Q.iter n f x) := by
  induction n generalizing x with
  | zero =>
      by_cases hx : dead x
      · simp [HybridCTMC.Kernel.trajectory, nnReward_pure,
          HybridCTMC.Kernel.survivingReward, HybridCTMC.Kernel.exited,
          hx, hdead x hx, SubMarkov.iter]
      · simp [HybridCTMC.Kernel.trajectory, nnReward_pure,
          HybridCTMC.Kernel.survivingReward, HybridCTMC.Kernel.exited,
          hx, SubMarkov.iter]
  | succ n ih =>
      rw [HybridCTMC.Kernel.trajectory, nnReward_bind]
      simp only [nnReward_map]
      rw [sourceIter_succ_left]
      by_cases hx : dead x
      · rw [hstep]
        simp [HybridCTMC.Kernel.survivingReward, HybridCTMC.Kernel.exited,
          hx, nnReward]
      · have hcont (y : S) :
            nnReward (K.trajectory n y)
              (fun xs => HybridCTMC.Kernel.survivingReward (fun z => ¬ dead z)
                (fun ys => ENNReal.ofReal (f (ys.getLastD x))) (x :: xs)) =
              ENNReal.ofReal (Q.iter n f y) := by
          calc
            _ = nnReward (K.trajectory n y)
                (HybridCTMC.Kernel.survivingReward (fun z => ¬ dead z)
                  (fun xs => ENNReal.ofReal (f (xs.getLastD y)))) := by
              apply nnReward_congr_support
              intro xs hxs
              have hn := K.trajectory_support_nonempty n y xs hxs
              have he : (x :: xs).getLastD x = xs.getLastD y := by
                cases xs with
                | nil => exact (hn rfl).elim
                | cons z zs => rfl
              have hexit : HybridCTMC.Kernel.exited (fun z => ¬ dead z) (x :: xs) =
                  HybridCTMC.Kernel.exited (fun z => ¬ dead z) xs := by
                apply propext
                simp [HybridCTMC.Kernel.exited, hx]
              simp only [HybridCTMC.Kernel.survivingReward, hexit, he]
            _ = _ := ih y
        simp_rw [hcont]
        have hk : kill dead (Q.iter n f) = Q.iter n f := by
          funext y
          by_cases hy : dead y
          · simp [kill, hy, sourceIter_dead_zero K Q dead hstep hdead n y hy]
          · simp [kill, hy]
        rw [hstep]
        simp only [hx, ite_false, hk]
        exact nnReward_kernel_ofReal K (Q.iter n f) (sourceIter_nonneg Q hf n) x

end FiniteHistories

section SourceExpectations

variable {S : Type} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [MeasurableSingletonClass S]
  {L Lam : ℝ} {G : (S → ℝ) → S → ℝ}

/-- Actual physical no-exit endpoint expectation equals the literal source
killed CT operator. A zero endpoint reward on dead states settles the source's
zero-tick term for every initial state, including a dead one. -/
theorem uniformized_noExit_endpoint_ct_zero_on_dead
    (hG : IsGen L G) (hLam : 0 < Lam) (hL : L ≤ Lam)
    (dead : S → Prop) (f : S → ℝ) (hf : ∀ y, 0 ≤ f y)
    (hdead : ∀ y, dead y → f y = 0) {T : ℝ} (hT : 0 ≤ T) (x : S) :
    (∫⁻ w, if HybridCTMC.Kernel.noExit (fun y => ¬ dead y) T w then
        ENNReal.ofReal (f (HybridCTMC.Kernel.timedState T w)) else 0
      ∂(uniformizedKernel hG hLam hL).eventLaw Lam hLam x) =
      ENNReal.ofReal ((generatorKilled hG hLam hL dead).ct (Lam * T) f x) := by
  let K := uniformizedKernel hG hLam hL
  let Q := generatorKilled hG hLam hL dead
  let r : ℝ≥0 := ⟨Lam * T, mul_nonneg hLam.le hT⟩
  have hstep (g : S → ℝ) (y : S) :
      Q.P g y = if dead y then 0 else K.expect (kill dead g) y :=
    stepK_as_stochastic_kernel hG hLam hL dead g y
  have hend (w : ℕ → ℝ × S) :
      (HybridCTMC.Kernel.timedHistory T w).getLastD x =
        HybridCTMC.Kernel.timedState T w :=
    HybridCTMC.Kernel.statePrefix_getLastD _ w x
  calc
    _ = nnReward (K.poissonTrajectory r x)
        (HybridCTMC.Kernel.survivingReward (fun y => ¬ dead y)
          (fun xs => ENNReal.ofReal (f (xs.getLastD x)))) := by
      simpa only [hend] using
        K.noExit_history_reward (fun y => ¬ dead y) hLam hT x
          (fun xs => ENNReal.ofReal (f (xs.getLastD x)))
    _ = ∑' n : ℕ, ENNReal.ofReal (pois (Lam * T) n) *
        ENNReal.ofReal (Q.iter n f x) := by
      rw [HybridCTMC.Kernel.poissonTrajectory, nnReward_bind, nnReward]
      apply tsum_congr
      intro n
      rw [trajectory_surviving_endpoint K Q dead hstep f hf hdead,
        Measure.toPMF_apply, ProbabilityTheory.poissonMeasure_singleton]
      congr 1
      apply congrArg ENNReal.ofReal
      change Real.exp (-(Lam * T)) * (Lam * T) ^ n / (n.factorial : ℝ) =
        Real.exp (-(Lam * T)) * ((Lam * T) ^ n / (n.factorial : ℝ))
      ring
    _ = ∑' n : ℕ, ENNReal.ofReal (pois (Lam * T) n * Q.iter n f x) := by
      apply tsum_congr
      intro n
      exact (ENNReal.ofReal_mul (sourcePois_nonneg (mul_nonneg hLam.le hT) n)).symm
    _ = ENNReal.ofReal (∑' n : ℕ, pois (Lam * T) n * Q.iter n f x) :=
      (ENNReal.ofReal_tsum_of_nonneg
        (fun n => mul_nonneg (sourcePois_nonneg (mul_nonneg hLam.le hT) n)
          (sourceIter_nonneg Q hf n x))
        (sourceCT_summable Q hf (mul_nonneg hLam.le hT) x)).symm
    _ = _ := rfl

/-- Exact zero-tick boundary condition at this initial state only. In particular,
this covers a dead initial state when the service reward is zero there after a
ledger reset; no global vanishing-on-dead premise is needed. -/
theorem uniformized_noExit_endpoint_ct_zero_tick
    (hG : IsGen L G) (hLam : 0 < Lam) (hL : L ≤ Lam)
    (dead : S → Prop) (f : S → ℝ) (hf : ∀ y, 0 ≤ f y)
    {T : ℝ} (hT : 0 ≤ T) (x : S) (hzero : dead x → f x = 0) :
    (∫⁻ w, if HybridCTMC.Kernel.noExit (fun y => ¬ dead y) T w then
        ENNReal.ofReal (f (HybridCTMC.Kernel.timedState T w)) else 0
      ∂(uniformizedKernel hG hLam hL).eventLaw Lam hLam x) =
      ENNReal.ofReal ((generatorKilled hG hLam hL dead).ct (Lam * T) f x) := by
  let Q := generatorKilled hG hLam hL dead
  have hkill : ∀ y, 0 ≤ kill dead f y := by
    intro y
    by_cases hy : dead y <;> simp [kill, hy, hf y]
  have hz : ∀ y, dead y → kill dead f y = 0 := by
    intro y hy
    simp [kill, hy]
  have hp : Q.P (kill dead f) = Q.P f := by
    funext y
    change stepK G Lam dead (kill dead f) y = stepK G Lam dead f y
    by_cases hy : dead y
    · simp [stepK, hy]
    · have hk : kill dead (kill dead f) = kill dead f := by
        funext z
        by_cases hz : dead z <;> simp [kill, hz]
      simp [stepK, hy, kill, hk]
  have hi (n : ℕ) : Q.iter n (kill dead f) x = Q.iter n f x := by
    cases n with
    | zero =>
        by_cases hx : dead x
        · simp [SubMarkov.iter, kill, hx, hzero hx]
        · simp [SubMarkov.iter, kill, hx]
    | succ n => change Q.iter n (Q.P (kill dead f)) x = Q.iter n (Q.P f) x; rw [hp]
  have hc : Q.ct (Lam * T) (kill dead f) x = Q.ct (Lam * T) f x := by
    unfold SubMarkov.ct
    apply tsum_congr
    intro n
    rw [hi]
  calc
    _ = ∫⁻ w, if HybridCTMC.Kernel.noExit (fun y => ¬ dead y) T w then
          ENNReal.ofReal (kill dead f (HybridCTMC.Kernel.timedState T w)) else 0
        ∂(uniformizedKernel hG hLam hL).eventLaw Lam hLam x := by
      apply lintegral_congr
      intro w
      by_cases hw : HybridCTMC.Kernel.noExit (fun y => ¬ dead y) T w
      · simp [hw, kill, hw T hT le_rfl]
      · simp [hw]
    _ = ENNReal.ofReal (Q.ct (Lam * T) (kill dead f) x) :=
      uniformized_noExit_endpoint_ct_zero_on_dead hG hLam hL dead (kill dead f)
        hkill hz hT x
    _ = _ := congrArg ENNReal.ofReal hc

/-- Standard safe-start version: no restriction on the nonnegative endpoint
reward outside the safe region is needed. No new initial killing is inserted. -/
theorem uniformized_noExit_endpoint_ct
    (hG : IsGen L G) (hLam : 0 < Lam) (hL : L ≤ Lam)
    (dead : S → Prop) (f : S → ℝ) (hf : ∀ y, 0 ≤ f y)
    {T : ℝ} (hT : 0 ≤ T) (x : S) (hx : ¬ dead x) :
    (∫⁻ w, if HybridCTMC.Kernel.noExit (fun y => ¬ dead y) T w then
        ENNReal.ofReal (f (HybridCTMC.Kernel.timedState T w)) else 0
      ∂(uniformizedKernel hG hLam hL).eventLaw Lam hLam x) =
      ENNReal.ofReal ((generatorKilled hG hLam hL dead).ct (Lam * T) f x) :=
  uniformized_noExit_endpoint_ct_zero_tick hG hLam hL dead f hf hT x
    (fun hd => (hx hd).elim)

/-- Concrete source-facing bridge: the actual finite capped CF3 path law has
the exact killed CT value of the original unbounded-ledger source on every
bounded-ledger observable. Its only initial-state premise is the actual floor/
safe test; rates, quotient identity, and the path law are constructed. -/
theorem cf3_source_noExit_endpoint_ct {p : FunctionalCapacity.Par}
    (hp : p.Valid) (Q D : ℕ) {Lam : ℝ} (hLam : 0 < Lam)
    (hRate : cf3Rate p ≤ Lam) (dead : CappedState p Q D → Prop)
    (f : CappedState p Q D → ℝ) (hf : ∀ y, 0 ≤ f y)
    {T : ℝ} (hT : 0 ≤ T) (x : CappedSource p)
    (hx : ¬ dead (capProject Q D x))
    [MeasurableSpace (CappedState p Q D)]
    [MeasurableSingletonClass (CappedState p Q D)] :
    (∫⁻ w, if HybridCTMC.Kernel.noExit (fun y => ¬ dead y) T w then
        ENNReal.ofReal (f (HybridCTMC.Kernel.timedState T w)) else 0
      ∂(uniformizedKernel (cappedGen_isGen hp Q D) hLam hRate).eventLaw
        Lam hLam (capProject Q D x)) =
      ENNReal.ofReal ((cf3SourceKilled hp hLam hRate
        (fun y => dead (capProject Q D y))).ct (Lam * T)
          (fun y => f (capProject Q D y)) x) := by
  calc
    _ = ENNReal.ofReal ((cf3CappedKilled hp Q D hLam hRate dead).ct (Lam * T)
        f (capProject Q D x)) :=
      uniformized_noExit_endpoint_ct (cappedGen_isGen hp Q D) hLam hRate dead
        f hf hT (capProject Q D x) hx
    _ = _ := congrArg ENNReal.ofReal
      (cf3_capped_ct hp Q D hLam hRate dead (Lam * T) f x).symm

end SourceExpectations

end
end CTMCHeredity20261019

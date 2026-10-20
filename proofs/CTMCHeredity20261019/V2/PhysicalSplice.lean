module

public import proofs.CTMCHeredity20261019.PhysicalCutJointLaw
public import proofs.CTMCHeredity20261019.PhysicalCutGlobalLaw

@[expose] public section

/-!
# Version 2: physical splicing of an executed prefix and an actual fresh future

Only the finite prefix actually executed through T is retained. The right
coordinate-zero sentinel is ignored. The first positive right hold is added
to the age of the current left holding interval, so no artificial proposal is
inserted at T. The discarded infinite left tail is never conditioned to be
independent of its actual physical cut.

The measure identity follows from the sealed joint finite-prefix/whole-future
law on each arrival slice, followed by the actual arrival-slice partition.
No Markov or spliced-law equality premise is assumed.
-/

namespace CTMCHeredity20261019.V2.PhysicalSplice

open MeasureTheory ProbabilityTheory Preorder Set HybridCTMC.Kernel
open scoped ENNReal Classical
noncomputable section

abbrev Path (S : Type*) := ℕ → ℝ × S

/-- Splice a finite executed prefix and the positive coordinates of a fresh
right path. Its incoming first hold includes the already elapsed left age. -/
def prefixSplice {S : Type*} (n : ℕ) (T : ℝ)
    (z : CutPrefix S n × Path S) : Path S := fun k =>
  if hk : k ≤ n then z.1 ⟨k, Finset.mem_Iic.mpr hk⟩
  else if k = n + 1 then
    (T - cutPrefixArrival n z.1 + (z.2 1).1, (z.2 1).2)
  else z.2 (k - n)

/-- The source's actual clock index chooses the executed finite left prefix. -/
def splice {S : Type*} (T : ℝ) (z : Path S × Path S) : Path S :=
  prefixSplice (clockIndex T z.1) T
    (frestrictLe (π := fun _ : ℕ => ℝ × S) (clockIndex T z.1) z.1, z.2)

@[simp] theorem prefixSplice_prefix {S : Type*} (n : ℕ) (T : ℝ)
    (u : CutPrefix S n) (v : Path S) (k : ℕ) (hk : k ≤ n) :
    prefixSplice n T (u, v) k = u ⟨k, Finset.mem_Iic.mpr hk⟩ := by
  simp only [prefixSplice, dite_eq_left hk]

@[simp] theorem prefixSplice_first {S : Type*} (n : ℕ) (T : ℝ)
    (u : CutPrefix S n) (v : Path S) :
    prefixSplice n T (u, v) (n + 1) =
      (T - cutPrefixArrival n u + (v 1).1, (v 1).2) := by
  simp [prefixSplice]

theorem prefixSplice_later {S : Type*} (n : ℕ) (T : ℝ)
    (u : CutPrefix S n) (v : Path S) (k : ℕ) (hk : n + 1 < k) :
    prefixSplice n T (u, v) k = v (k - n) := by
  have hle : ¬ k ≤ n := by omega
  have hne : k ≠ n + 1 := by omega
  simp only [prefixSplice, dite_eq_right hle, hne, ite_false]

/-- The splice ignores the right coordinate-zero sentinel entirely. -/
theorem prefixSplice_congr_positive {S : Type*} (n : ℕ) (T : ℝ)
    (u : CutPrefix S n) (v r : Path S) (h : ∀ k : ℕ, 0 < k → v k = r k) :
    prefixSplice n T (u, v) = prefixSplice n T (u, r) := by
  funext k
  by_cases hk : k ≤ n
  · rw [prefixSplice_prefix n T u v k hk, prefixSplice_prefix n T u r k hk]
  · by_cases he : k = n + 1
    · subst k
      rw [prefixSplice_first, prefixSplice_first, h 1 (by decide)]
    · have hkn : n + 1 < k := by omega
      rw [prefixSplice_later n T u v k hkn, prefixSplice_later n T u r k hkn,
        h (k - n) (by omega)]

theorem measurable_prefixSplice {S : Type*} [MeasurableSpace S] (n : ℕ) (T : ℝ) :
    Measurable (prefixSplice (S := S) n T) := by
  apply measurable_pi_iff.mpr
  intro k
  by_cases hk : k ≤ n
  · simp only [prefixSplice, dite_eq_left hk]
    exact (measurable_pi_apply (X := fun _ : Finset.Iic n => ℝ × S)
      ⟨k, Finset.mem_Iic.mpr hk⟩).comp measurable_fst
  · simp only [prefixSplice, dite_eq_right hk]
    by_cases he : k = n + 1
    · simp only [ite_eq_left he]
      have hr : Measurable (fun z : CutPrefix S n × Path S => z.2 1) :=
        (measurable_pi_apply (X := fun _ : ℕ => ℝ × S) 1).comp measurable_snd
      exact ((measurable_const.sub ((measurable_cutPrefixArrival n).comp measurable_fst)).add
        hr.fst).prodMk hr.snd
    · simp only [ite_eq_right he]
      exact (measurable_pi_apply (X := fun _ : ℕ => ℝ × S) (k - n)).comp measurable_snd

theorem measurable_splice {S : Type*} [MeasurableSpace S] (T : ℝ) :
    Measurable (splice (S := S) T) := by
  have hi (n : ℕ) : Measurable (fun z : Path S × Path S =>
      prefixSplice n T (frestrictLe (π := fun _ : ℕ => ℝ × S) n z.1, z.2)) := by
    exact (measurable_prefixSplice n T).comp
      (((measurable_frestrictLe n).comp measurable_fst).prodMk measurable_snd)
  have hm : Measurable (fun z : (Path S × Path S) × ℕ =>
      prefixSplice z.2 T (frestrictLe (π := fun _ : ℕ => ℝ × S) z.2 z.1.1, z.1.2)) :=
    measurable_from_prod_countable_left hi
  change Measurable (fun z : Path S × Path S =>
    prefixSplice (clockIndex T z.1) T
      (frestrictLe (π := fun _ : ℕ => ℝ × S) (clockIndex T z.1) z.1, z.2))
  simpa only [Function.comp_def, id_eq] using
    hm.comp (measurable_id.prodMk ((measurable_clockIndex T).comp measurable_fst))

/-- Splicing the actual finite prefix to its actual physical cut recovers the
entire original sequence. Positivity identifies clipped and original holds. -/
theorem prefixSplice_physicalCut {S : Type*} (w : Path S) (n : ℕ) (T : ℝ)
    (hp : ∀ k : ℕ, 0 < (w (k + 1)).1) :
    prefixSplice n T
      (frestrictLe (π := fun _ : ℕ => ℝ × S) n w, physicalCut w n T) = w := by
  funext k
  by_cases hk : k ≤ n
  · rw [prefixSplice_prefix n T _ _ k hk]
    rfl
  · by_cases he : k = n + 1
    · subst k
      rw [prefixSplice_first, cutPrefixArrival_frestrict, physicalCut_one]
      apply Prod.ext
      · have ha := physicalCut_arrival_next w n
        rw [max_eq_right (hp n).le] at ha
        dsimp only [Prod.fst]
        linarith
      · rfl
    · have hkn : n + 1 < k := by omega
      rw [prefixSplice_later n T _ _ k hkn]
      have heq : k - n = (k - n - 2) + 2 := by omega
      rw [heq, physicalCut_later]
      congr 1
      omega

theorem splice_physicalTimedCut {S : Type*} (T : ℝ) (w : Path S)
    (hp : ∀ k : ℕ, 0 < (w (k + 1)).1) :
    splice T (w, physicalTimedCut T w) = w :=
  prefixSplice_physicalCut w (clockIndex T w) T hp

section ActualLaw

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- An arbitrary joint finite-prefix/whole-future reward has its actual fresh
conditional value on an arrival slice. This follows twice from the sealed
joint law; the second reward is constant in its future coordinate. -/
theorem eventLaw_slice_joint_fresh (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (n : ℕ) (T : ℝ)
    (G : CutPrefix S n × Path S → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ w, if arrivalSlice T n w then
        G (frestrictLe (π := fun _ : ℕ => ℝ × S) n w, physicalCut w n T) else 0
      ∂K.eventLaw Lam hLam x) =
      ∫⁻ w, if arrivalSlice T n w then
        (∫⁻ v, G (frestrictLe (π := fun _ : ℕ => ℝ × S) n w, v)
          ∂K.eventLaw Lam hLam (w n).2) else 0 ∂K.eventLaw Lam hLam x := by
  let q : CutPrefix S n → ℝ≥0∞ := fun u =>
    ∫⁻ v, G (u, v) ∂prefixFreshEventKernel K hLam n u
  have hq : Measurable q := hG.lintegral_kernel_prod_right'
  have hr := eventLaw_physicalCut_joint_reward K hLam x n T G hG
  have hi := eventLaw_physicalCut_joint_reward K hLam x n T
    (fun z : CutPrefix S n × Path S => q z.1) (hq.comp measurable_fst)
  simp only [lintegral_const, measure_univ, mul_one] at hi
  convert (hr.trans hi.symm) using 1 <;> apply lintegral_congr <;> intro w
  all_goals
    by_cases hw : arrivalTime n w ≤ T ∧ T < arrivalTime (n + 1) w
    · have hs : arrivalSlice T n w := hw
      simp only [ite_eq_left hw, ite_eq_left hs, q, prefixFreshEventKernel,
        ProbabilityTheory.Kernel.coe_mk, frestrictLe_apply]
    · have hs : ¬ arrivalSlice T n w := hw
      simp only [ite_eq_right hw, ite_eq_right hs]

/-- Resample an actual fresh right path conditionally on the actual physical
state of the left path. The unexecuted left tail is merely auxiliary. -/
def continuationKernel (K : HybridCTMC.Kernel S) {Lam : ℝ} (hLam : 0 < Lam) (T : ℝ) :
    ProbabilityTheory.Kernel (Path S) (Path S) where
  toFun w := K.eventLaw Lam hLam (timedState T w)
  measurable' := (measurable_of_countable (fun y : S => K.eventLaw Lam hLam y)).comp
    (measurable_timedState T)

instance continuationKernel_markov (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (T : ℝ) : IsMarkovKernel (continuationKernel K hLam T) where
  isProbabilityMeasure w := by
    change IsProbabilityMeasure (K.eventLaw Lam hLam (timedState T w))
    infer_instance

variable [StandardBorelSpace S]

/-- The actual left/fresh-right conditional composition has precisely the
original event-law expectation after physical splicing. -/
theorem eventLaw_splice_lintegral (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (T : ℝ) (hT : 0 ≤ T)
    (F : Path S → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F (splice T z)
      ∂(K.eventLaw Lam hLam x).compProd (continuationKernel K hLam T)) =
      ∫⁻ w, F w ∂K.eventLaw Lam hLam x := by
  let G (n : ℕ) : CutPrefix S n × Path S → ℝ≥0∞ := fun z => F (prefixSplice n T z)
  have hG (n : ℕ) : Measurable (G n) := by
    simpa only [G, Function.comp_def] using hF.comp (measurable_prefixSplice n T)
  let q (n : ℕ) (u : CutPrefix S n) : ℝ≥0∞ :=
    ∫⁻ v, G n (u, v) ∂prefixFreshEventKernel K hLam n u
  have hq (n : ℕ) : Measurable (q n) := (hG n).lintegral_kernel_prod_right'
  let H (n : ℕ) (w : Path S) : ℝ≥0∞ := q n (frestrictLe n w)
  have hH (n : ℕ) : Measurable (H n) := (hq n).comp (measurable_frestrictLe n)
  let J (n : ℕ) (w : Path S) : ℝ≥0∞ :=
    G n (frestrictLe (π := fun _ : ℕ => ℝ × S) n w, physicalCut w n T)
  have hJ (n : ℕ) : Measurable (J n) := (hG n).comp
    ((measurable_frestrictLe n).prodMk (measurable_physicalCut n T))
  have hcomp : Measurable (fun z : Path S × Path S => F (splice T z)) := by
    simpa only [Function.comp_def] using hF.comp (measurable_splice T)
  calc
    _ = ∫⁻ w, ∫⁻ v, F (splice T (w, v))
        ∂K.eventLaw Lam hLam (timedState T w) ∂K.eventLaw Lam hLam x :=
      Measure.lintegral_compProd
        (μ := K.eventLaw Lam hLam x) (κ := continuationKernel K hLam T) hcomp
    _ = ∫⁻ w, H (clockIndex T w) w ∂K.eventLaw Lam hLam x := by
      apply lintegral_congr
      intro w
      rfl
    _ = ∑' n : ℕ, ∫⁻ w, arrivalSliceValue T H n w ∂K.eventLaw Lam hLam x :=
      lintegral_arrivalSlice_partition K hLam x T hT H hH
    _ = ∑' n : ℕ, ∫⁻ w, arrivalSliceValue T J n w ∂K.eventLaw Lam hLam x := by
      apply tsum_congr
      intro n
      symm
      exact eventLaw_slice_joint_fresh K hLam x n T (G n) (hG n)
    _ = ∫⁻ w, J (clockIndex T w) w ∂K.eventLaw Lam hLam x :=
      (lintegral_arrivalSlice_partition K hLam x T hT J hJ).symm
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [K.ae_holding_pos hLam x] with w hw
      change F (splice T (w, physicalTimedCut T w)) = F w
      exact congrArg F (splice_physicalTimedCut T w hw)

/-- Whole physical splice law for the actual conditional product. -/
theorem eventLaw_splice (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (T : ℝ) (hT : 0 ≤ T) :
    ((K.eventLaw Lam hLam x).compProd (continuationKernel K hLam T)).map (splice T) =
      K.eventLaw Lam hLam x := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (measurable_splice T)]
  exact eventLaw_splice_lintegral K hLam x T hT F hF

omit [StandardBorelSpace S] in
theorem ae_splice_physicalTimedCut (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (T : ℝ) :
    ∀ᵐ w ∂K.eventLaw Lam hLam x, splice T (w, physicalTimedCut T w) = w := by
  filter_upwards [K.ae_holding_pos hLam x] with w hw
  exact splice_physicalTimedCut T w hw

end ActualLaw

end
end CTMCHeredity20261019.V2.PhysicalSplice

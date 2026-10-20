module

public import proofs.CTMCHeredity20261019.EventIndexSuffix
public import proofs.CTMCHeredity20261019.PrefixCutResidual
public import proofs.CTMCHeredity20261019.PhysicalCut

@[expose] public section

/-!
# Authentic finite-cylinder laws for the physical residual suffix

On each literal arrival slice `arrivalTime n ≤ T < arrivalTime (n+1)`, the
future physical cut has the finite-coordinate cylinder law of a fresh actual
`eventLaw` from the state at event n, multiplied by the exact prefix survival
weight. The first reward may depend jointly on the complete prefix and the
residual hold/state pair, so arbitrary measurable prefix rewards are included.

The proof first eliminates the later finite cylinder by the deterministic
event-index suffix theorem, then applies the actual residual-clock theorem,
and finally recognizes the fresh event-law expectation. No conditional suffix
hypothesis is assumed. Infinite-suffix equality and summing all arrival slices
remain distinct obligations.
-/

namespace CTMCHeredity20261019

open MeasureTheory ProbabilityTheory Preorder Set HybridCTMC.Kernel
open scoped BigOperators ENNReal
noncomputable section

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- Every post-residual holding coordinate is exactly the corresponding
source suffix coordinate; this equality is deterministic on every sequence. -/
theorem futureCylinderWeight_physicalCut (n k : ℕ) (T : ℝ)
    (f : ℕ → ℝ × S → ℝ≥0∞) (w : ℕ → ℝ × S) :
    futureCylinderWeight 1 k f (physicalCut w n T) =
      futureCylinderWeight (n + 1) k f w := by
  unfold futureCylinderWeight
  apply Finset.prod_congr rfl
  intro i _
  have h1 : 1 + i + 1 = i + 2 := by omega
  have h2 : n + 1 + i + 1 = n + i + 2 := by omega
  rw [h1, physicalCut_later, h2]

/-- The first future coordinate under the actual source event law has its
actual `clockStep` distribution, derived from prefix disintegration. -/
theorem eventLaw_first_reward (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (A : ℝ × S → ℝ≥0∞) (hA : Measurable A) :
    (∫⁻ v, A (v 1) ∂K.eventLaw Lam hLam x) = ∫⁻ z, A z ∂K.clockStep Lam x := by
  let q : S → ℝ≥0∞ := fun y => ∫⁻ z, A z ∂K.clockStep Lam y
  have hq : Measurable q := measurable_of_countable q
  have hQ : Measurable (fun u : EventPrefix S 0 =>
      q (u ⟨0, Finset.mem_Iic.mpr le_rfl⟩).2) :=
    hq.comp (measurable_pi_apply (X := fun _ : Finset.Iic 0 => ℝ × S)
      ⟨0, Finset.mem_Iic.mpr le_rfl⟩).snd
  calc
    _ = ∫⁻ u, q (u ⟨0, Finset.mem_Iic.mpr le_rfl⟩).2
        ∂((K.eventLaw Lam hLam x).map (frestrictLe (π := fun _ : ℕ => ℝ × S) 0)) :=
      K.eventLaw_lintegral_prefix_step hLam x 0
        (fun p : EventPrefix S 0 × (ℝ × S) => A p.2) (hA.comp measurable_snd)
    _ = ∫⁻ v, q (v 0).2 ∂K.eventLaw Lam hLam x := by
      apply (lintegral_map hQ (measurable_frestrictLe 0)).trans
      apply lintegral_congr
      intro v
      rfl
    _ = q x := by
      have he : (fun v : ℕ → ℝ × S => q (v 0).2) =ᵐ[K.eventLaw Lam hLam x]
          fun _ => q x := by
        filter_upwards [K.ae_event_initial hLam x] with v hv
        rw [hv]
      rw [lintegral_congr_ae he]
      simp

/-- A fresh process's first hold/state reward followed by any finite future
cylinder is precisely one actual clock step followed by its proved continuation. -/
theorem eventLaw_first_continuation (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (k : ℕ)
    (A : ℝ × S → ℝ≥0∞) (hA : Measurable A)
    (f : ℕ → ℝ × S → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) (g : S → ℝ≥0∞) :
    (∫⁻ v, A (v 1) * futureCylinderWeight 1 k f v * g (v (k + 1)).2
      ∂K.eventLaw Lam hLam x) =
      ∫⁻ z, A z * futureCylinderValue K Lam f k g z.2 ∂K.clockStep Lam x := by
  let B : EventPrefix S 1 → ℝ≥0∞ := fun u =>
    A (u ⟨1, Finset.mem_Iic.mpr le_rfl⟩)
  have hB : Measurable B :=
    hA.comp (measurable_pi_apply (X := fun _ : Finset.Iic 1 => ℝ × S)
      ⟨1, Finset.mem_Iic.mpr le_rfl⟩)
  have hv : Measurable (futureCylinderValue K Lam f k g) := measurable_of_countable _
  have hcollapse := eventLaw_futureCylinder_collapse K hLam x 1 k B hB f hf g
  have hsum : 1 + k = k + 1 := by omega
  have hc : (∫⁻ v, A (v 1) * futureCylinderWeight 1 k f v * g (v (k + 1)).2
      ∂K.eventLaw Lam hLam x) =
      ∫⁻ v, A (v 1) * futureCylinderValue K Lam f k g (v 1).2
        ∂K.eventLaw Lam hLam x := by
    simpa only [B, frestrictLe_apply, hsum] using hcollapse
  exact hc.trans (eventLaw_first_reward K hLam x
    (fun z => A z * futureCylinderValue K Lam f k g z.2) (hA.mul (hv.comp measurable_snd)))

/-- Finite-cylinder physical-cut factorization on one authentic arrival slice.
`H` can contain any measurable prefix reward as well as the first residual
holding/state reward. The RHS uses the actual fresh `eventLaw` from the
current last state, not an assumed suffix law or only a backward recursion. -/
theorem eventLaw_physicalCut_cylinder_slice (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (n k : ℕ) (T : ℝ)
    (H : CutPrefix S n × (ℝ × S) → ℝ≥0∞) (hH : Measurable H)
    (f : ℕ → ℝ × S → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) (g : S → ℝ≥0∞) :
    (∫⁻ w, if arrivalTime n w ≤ T ∧ T < arrivalTime (n + 1) w then
        H (frestrictLe (π := fun _ : ℕ => ℝ × S) n w, physicalCut w n T 1) *
          futureCylinderWeight 1 k f (physicalCut w n T) * g (physicalCut w n T (k + 1)).2
      else 0 ∂K.eventLaw Lam hLam x) =
      ∫⁻ u, if cutPrefixArrival n u ≤ T then
          ENNReal.ofReal (Real.exp (-(Lam * (T - cutPrefixArrival n u)))) *
            (∫⁻ v, H (u, v 1) * futureCylinderWeight 1 k f v * g (v (k + 1)).2
              ∂K.eventLaw Lam hLam (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2)
        else 0
      ∂((K.eventLaw Lam hLam x).map (frestrictLe (π := fun _ : ℕ => ℝ × S) n)) := by
  let pr : EventPrefix S (n + 1) → EventPrefix S n :=
    frestrictLe₂ (π := fun _ : ℕ => ℝ × S) (Nat.le_succ n)
  let P : EventPrefix S (n + 1) → ℝ≥0∞ := fun u =>
    if cutPrefixArrival n (pr u) ≤ T ∧ T < cutPrefixArrival (n + 1) u then
      H (pr u, (cutPrefixArrival (n + 1) u - T,
        (u ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).2)) else 0
  let J : S → ℝ≥0∞ := futureCylinderValue K Lam f k g
  have hJ : Measurable J := measurable_of_countable J
  have hpr : Measurable pr := measurable_frestrictLe₂ (Nat.le_succ n)
  have ha : Measurable (fun u : EventPrefix S (n + 1) => cutPrefixArrival n (pr u)) :=
    (measurable_cutPrefixArrival n).comp hpr
  have hb : Measurable (cutPrefixArrival (S := S) (n + 1)) :=
    measurable_cutPrefixArrival (n + 1)
  have hP : Measurable P :=
    Measurable.ite
      ((measurableSet_le ha measurable_const).inter
        (measurableSet_lt measurable_const hb))
      (hH.comp (hpr.prodMk ((hb.sub measurable_const).prodMk
        (measurable_pi_apply (X := fun _ : Finset.Iic (n + 1) => ℝ × S)
          ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).snd))) measurable_const
  have hPpath (w : ℕ → ℝ × S) :
      P (frestrictLe (π := fun _ : ℕ => ℝ × S) (n + 1) w) =
        if arrivalTime n w ≤ T ∧ T < arrivalTime (n + 1) w then
          H (frestrictLe (π := fun _ : ℕ => ℝ × S) n w, physicalCut w n T 1) else 0 := by
    have hr : pr (frestrictLe (π := fun _ : ℕ => ℝ × S) (n + 1) w) =
        frestrictLe (π := fun _ : ℕ => ℝ × S) n w := rfl
    dsimp only [P]
    rw [hr, cutPrefixArrival_frestrict, cutPrefixArrival_frestrict]
    rfl
  let Q : CutPrefix S n × (ℝ × S) → ℝ≥0∞ := fun p => H p * J p.2.2
  have hQ : Measurable Q :=
    hH.mul (hJ.comp (measurable_snd.comp measurable_snd))
  calc
    _ = ∫⁻ w, P (frestrictLe (π := fun _ : ℕ => ℝ × S) (n + 1) w) *
        futureCylinderWeight (n + 1) k f w * g (w ((n + 1) + k)).2
        ∂K.eventLaw Lam hLam x := by
      apply lintegral_congr
      intro w
      rw [hPpath, futureCylinderWeight_physicalCut, physicalCut_state]
      have hi : n + (k + 1) = n + 1 + k := by omega
      rw [hi]
      by_cases hw : arrivalTime n w ≤ T ∧ T < arrivalTime (n + 1) w
      · simp only [hw, true_and, ite_true]
      · simp only [hw, ite_false, zero_mul]
    _ = ∫⁻ w, P (frestrictLe (π := fun _ : ℕ => ℝ × S) (n + 1) w) *
        J (w (n + 1)).2 ∂K.eventLaw Lam hLam x :=
      eventLaw_futureCylinder_collapse K hLam x (n + 1) k P hP f hf g
    _ = ∫⁻ w, if arrivalTime n w ≤ T ∧ T < arrivalTime (n + 1) w then
        Q (frestrictLe (π := fun _ : ℕ => ℝ × S) n w,
          (arrivalTime (n + 1) w - T, (w (n + 1)).2)) else 0
        ∂K.eventLaw Lam hLam x := by
      apply lintegral_congr
      intro w
      rw [hPpath]
      by_cases hw : arrivalTime n w ≤ T ∧ T < arrivalTime (n + 1) w
      · simp only [hw, true_and, ite_true, Q, physicalCut_one]
      · simp only [hw, ite_false, zero_mul]
    _ = ∫⁻ u, if cutPrefixArrival n u ≤ T then
        ENNReal.ofReal (Real.exp (-(Lam * (T - cutPrefixArrival n u)))) *
          ∫⁻ z, Q (u, z) ∂K.clockStep Lam (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2
        else 0
        ∂((K.eventLaw Lam hLam x).map (frestrictLe (π := fun _ : ℕ => ℝ × S) n)) :=
      eventLaw_arrival_slice_residual K hLam x n T Q hQ
    _ = _ := by
      apply lintegral_congr
      intro u
      by_cases hu : cutPrefixArrival n u ≤ T
      · simp only [hu, ite_true]
        change ENNReal.ofReal (Real.exp (-(Lam * (T - cutPrefixArrival n u)))) *
          (∫⁻ z, H (u, z) * futureCylinderValue K Lam f k g z.2
            ∂K.clockStep Lam (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2) = _
        rw [← eventLaw_first_continuation K hLam
          (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2 k
          (fun z => H (u, z)) (hH.comp measurable_prodMk_left) f hf g]
      · simp only [hu, ite_false]

end
end CTMCHeredity20261019

module

public import proofs.HybridCTMCInfrastructure.PrefixFactorization
public import proofs.HybridCTMCInfrastructure.ClockInitial
public import Mathlib.MeasureTheory.Group.Arithmetic

@[expose] public section

/-!
# Finite-cylinder Markov suffix laws for the actual event path

For every deterministic event index, every measurable prefix reward, and every
finite product of measurable future-coordinate rewards, the future is evaluated
by the actual fresh event law started at the last prefix state. A terminal
state reward is allowed as well. The proof repeatedly applies the existing
one-step prefix disintegration; no Markov or suffix-law hypothesis is assumed.

In particular, use the theorem at n+1 with a prefix reward containing a physical
cut and its first residual hold/state reward. The remaining future cylinder is
then a fresh-kernel recursion from the sampled next state. Identification of
arbitrary infinite-suffix events is not asserted in this module.
-/

namespace CTMCHeredity20261019

open MeasureTheory ProbabilityTheory Preorder Set
open scoped BigOperators ENNReal
noncomputable section

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

abbrev EventPrefix (S : Type*) (n : ℕ) := ∀ _ : Finset.Iic n, ℝ × S

/-- k future coordinates strictly after event n, without its incoming hold. -/
def futureCylinderWeight (n k : ℕ) (f : ℕ → ℝ × S → ℝ≥0∞)
    (w : ℕ → ℝ × S) : ℝ≥0∞ :=
  ∏ i ∈ Finset.range k, f i (w (n + i + 1))

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem futureCylinderWeight_succ (n k : ℕ) (f : ℕ → ℝ × S → ℝ≥0∞)
    (w : ℕ → ℝ × S) :
    futureCylinderWeight n (k + 1) f w =
      futureCylinderWeight n k f w * f k (w (n + k + 1)) := by
  simp only [futureCylinderWeight, Finset.prod_range_succ]

omit [Fintype S] [MeasurableSingletonClass S] in
theorem measurable_futureCylinderWeight (n k : ℕ) (f : ℕ → ℝ × S → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) : Measurable (futureCylinderWeight n k f) := by
  unfold futureCylinderWeight
  apply Finset.measurable_prod
  intro i _
  exact (hf i).comp (measurable_pi_apply (n + i + 1))

/-- The same future product represented on the finite prefix through n+k. -/
def prefixFutureWeight (n k : ℕ) (f : ℕ → ℝ × S → ℝ≥0∞)
    (u : EventPrefix S (n + k)) : ℝ≥0∞ :=
  ∏ i ∈ Finset.range k,
    if hi : n + i + 1 ≤ n + k then
      f i (u ⟨n + i + 1, Finset.mem_Iic.mpr hi⟩) else 1

omit [Fintype S] [MeasurableSingletonClass S] in
theorem measurable_prefixFutureWeight (n k : ℕ) (f : ℕ → ℝ × S → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) : Measurable (prefixFutureWeight n k f) := by
  unfold prefixFutureWeight
  apply Finset.measurable_prod
  intro i hi
  have hin : n + i + 1 ≤ n + k := by have := Finset.mem_range.mp hi; omega
  simp only [dite_eq_left hin]
  exact (hf i).comp (measurable_pi_apply (X := fun _ : Finset.Iic (n + k) => ℝ × S)
    ⟨n + i + 1, Finset.mem_Iic.mpr hin⟩)

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem prefixFutureWeight_frestrict (n k : ℕ) (f : ℕ → ℝ × S → ℝ≥0∞)
    (w : ℕ → ℝ × S) :
    prefixFutureWeight n k f (frestrictLe (π := fun _ : ℕ => ℝ × S) (n + k) w) =
      futureCylinderWeight n k f w := by
  unfold prefixFutureWeight futureCylinderWeight
  apply Finset.prod_congr rfl
  intro i hi
  rw [dite_eq_left (by have := Finset.mem_range.mp hi; omega)]
  rfl

/-- The actual backward finite-kernel recursion. At each step the joint
holding-time/next-state law is `clockStep`, not an abstract transition oracle. -/
def futureCylinderValue (K : HybridCTMC.Kernel S) (Lam : ℝ)
    (f : ℕ → ℝ × S → ℝ≥0∞) : ℕ → (S → ℝ≥0∞) → S → ℝ≥0∞
  | 0, g => g
  | k + 1, g => futureCylinderValue K Lam f k
      (fun y => ∫⁻ z, f k z * g z.2 ∂K.clockStep Lam y)

/-- Integrate the last future coordinate using the actual prefix-step law. -/
theorem eventLaw_futureCylinder_peel_last (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (n k : ℕ)
    (B : EventPrefix S n → ℝ≥0∞) (hB : Measurable B)
    (f : ℕ → ℝ × S → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) (g : S → ℝ≥0∞) :
    (∫⁻ w, B (frestrictLe (π := fun _ : ℕ => ℝ × S) n w) *
        futureCylinderWeight n (k + 1) f w * g (w (n + (k + 1))).2
      ∂K.eventLaw Lam hLam x) =
      ∫⁻ w, B (frestrictLe (π := fun _ : ℕ => ℝ × S) n w) *
        futureCylinderWeight n k f w *
          (∫⁻ z, f k z * g z.2 ∂K.clockStep Lam (w (n + k)).2)
      ∂K.eventLaw Lam hLam x := by
  let P : EventPrefix S (n + k) → ℝ≥0∞ := fun u =>
    B (frestrictLe₂ (π := fun _ : ℕ => ℝ × S) (Nat.le_add_right n k) u) *
      prefixFutureWeight n k f u
  let q : S → ℝ≥0∞ := fun y => ∫⁻ z, f k z * g z.2 ∂K.clockStep Lam y
  let G : EventPrefix S (n + k) × (ℝ × S) → ℝ≥0∞ := fun p =>
    P p.1 * (f k p.2 * g p.2.2)
  have hg : Measurable g := measurable_of_countable g
  have hq : Measurable q := measurable_of_countable q
  have hP : Measurable P :=
    (hB.comp (measurable_frestrictLe₂ (Nat.le_add_right n k))).mul
      (measurable_prefixFutureWeight n k f hf)
  have hG : Measurable G :=
    (hP.comp measurable_fst).mul
      (((hf k).comp measurable_snd).mul (hg.comp (measurable_snd.comp measurable_snd)))
  have hPpath (w : ℕ → ℝ × S) :
      P (frestrictLe (π := fun _ : ℕ => ℝ × S) (n + k) w) =
        B (frestrictLe (π := fun _ : ℕ => ℝ × S) n w) * futureCylinderWeight n k f w := by
    dsimp only [P]
    rw [prefixFutureWeight_frestrict]
    rfl
  have hH : Measurable (fun u : EventPrefix S (n + k) =>
      P u * q (u ⟨n + k, Finset.mem_Iic.mpr le_rfl⟩).2) :=
    hP.mul (hq.comp (measurable_pi_apply (X := fun _ : Finset.Iic (n + k) => ℝ × S)
      ⟨n + k, Finset.mem_Iic.mpr le_rfl⟩).snd)
  calc
    _ = ∫⁻ w, G (frestrictLe (π := fun _ : ℕ => ℝ × S) (n + k) w,
        w ((n + k) + 1)) ∂K.eventLaw Lam hLam x := by
      apply lintegral_congr
      intro w
      dsimp only [G]
      rw [hPpath, futureCylinderWeight_succ]
      simp only [Nat.add_assoc, mul_assoc]
    _ = ∫⁻ u, ∫⁻ z, G (u, z)
        ∂K.clockStep Lam (u ⟨n + k, Finset.mem_Iic.mpr le_rfl⟩).2
        ∂((K.eventLaw Lam hLam x).map
          (frestrictLe (π := fun _ : ℕ => ℝ × S) (n + k))) :=
      K.eventLaw_lintegral_prefix_step hLam x (n + k) G hG
    _ = ∫⁻ u, P u * q (u ⟨n + k, Finset.mem_Iic.mpr le_rfl⟩).2
        ∂((K.eventLaw Lam hLam x).map
          (frestrictLe (π := fun _ : ℕ => ℝ × S) (n + k))) := by
      apply lintegral_congr
      intro u
      exact lintegral_const_mul (P u) ((hf k).mul (hg.comp measurable_snd))
    _ = ∫⁻ w, P (frestrictLe (π := fun _ : ℕ => ℝ × S) (n + k) w) *
        q (w (n + k)).2 ∂K.eventLaw Lam hLam x := by
      apply (lintegral_map hH (measurable_frestrictLe (n + k))).trans
      apply lintegral_congr
      intro w
      rfl
    _ = _ := by
      apply lintegral_congr
      intro w
      rw [hPpath]

/-- Finite future cylinders collapse to a state-only kernel recursion while
the entire earlier prefix reward is retained. -/
theorem eventLaw_futureCylinder_collapse (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (n k : ℕ)
    (B : EventPrefix S n → ℝ≥0∞) (hB : Measurable B)
    (f : ℕ → ℝ × S → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) (g : S → ℝ≥0∞) :
    (∫⁻ w, B (frestrictLe (π := fun _ : ℕ => ℝ × S) n w) *
        futureCylinderWeight n k f w * g (w (n + k)).2 ∂K.eventLaw Lam hLam x) =
      ∫⁻ w, B (frestrictLe (π := fun _ : ℕ => ℝ × S) n w) *
        futureCylinderValue K Lam f k g (w n).2 ∂K.eventLaw Lam hLam x := by
  induction k generalizing g with
  | zero => simp [futureCylinderWeight, futureCylinderValue]
  | succ k ih =>
    rw [eventLaw_futureCylinder_peel_last K hLam x n k B hB f hf g]
    exact ih (fun y => ∫⁻ z, f k z * g z.2 ∂K.clockStep Lam y)

/-- The recursion is exactly the cylinder expectation under the constructed
fresh event law, rather than a separately assumed Markov transition. -/
theorem eventLaw_futureCylinder_value (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (k : ℕ)
    (f : ℕ → ℝ × S → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) (g : S → ℝ≥0∞) :
    (∫⁻ w, futureCylinderWeight 0 k f w * g (w k).2 ∂K.eventLaw Lam hLam x) =
      futureCylinderValue K Lam f k g x := by
  have h := eventLaw_futureCylinder_collapse K hLam x 0 k
    (fun _ => 1) measurable_const f hf g
  simp only [one_mul, Nat.zero_add] at h
  rw [h]
  have he : (fun w : ℕ → ℝ × S => futureCylinderValue K Lam f k g (w 0).2)
      =ᵐ[K.eventLaw Lam hLam x] fun _ => futureCylinderValue K Lam f k g x := by
    filter_upwards [K.ae_event_initial hLam x] with w hw
    rw [hw]
  rw [lintegral_congr_ae he]
  simp

/-- The deterministic event-index Markov suffix law for all finite coordinate
cylinder rewards. The fresh process has coordinate zero `(0,last state)` by
`ae_event_initial`; the incoming holding time at n is not reused. -/
theorem eventLaw_futureCylinder_disintegrate (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (n k : ℕ)
    (B : EventPrefix S n → ℝ≥0∞) (hB : Measurable B)
    (f : ℕ → ℝ × S → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) (g : S → ℝ≥0∞) :
    (∫⁻ w, B (frestrictLe (π := fun _ : ℕ => ℝ × S) n w) *
        futureCylinderWeight n k f w * g (w (n + k)).2 ∂K.eventLaw Lam hLam x) =
      ∫⁻ u, B u *
        (∫⁻ v, futureCylinderWeight 0 k f v * g (v k).2
          ∂K.eventLaw Lam hLam (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2)
      ∂((K.eventLaw Lam hLam x).map (frestrictLe (π := fun _ : ℕ => ℝ × S) n)) := by
  have hv : Measurable (futureCylinderValue K Lam f k g) :=
    measurable_of_countable _
  have hH : Measurable (fun u : EventPrefix S n =>
      B u * futureCylinderValue K Lam f k g (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2) :=
    hB.mul (hv.comp (measurable_pi_apply (X := fun _ : Finset.Iic n => ℝ × S)
      ⟨n, Finset.mem_Iic.mpr le_rfl⟩).snd)
  rw [eventLaw_futureCylinder_collapse K hLam x n k B hB f hf g]
  calc
    _ = ∫⁻ u, B u * futureCylinderValue K Lam f k g
        (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2
        ∂((K.eventLaw Lam hLam x).map (frestrictLe (π := fun _ : ℕ => ℝ × S) n)) := by
      symm
      apply (lintegral_map hH (measurable_frestrictLe n)).trans
      apply lintegral_congr
      intro w
      rfl
    _ = _ := by
      apply lintegral_congr
      intro u
      rw [eventLaw_futureCylinder_value K hLam _ k f hf g]

/-- Conventional normalized suffix: discard the incoming hold at n, install a
zero hold at coordinate zero, and retain every later actual hold and state. -/
def normalizedEventSuffix (n : ℕ) (w : ℕ → ℝ × S) : ℕ → ℝ × S
  | 0 => (0, (w n).2)
  | j + 1 => w (n + j + 1)

omit [Fintype S] [MeasurableSingletonClass S] in
theorem measurable_normalizedEventSuffix (n : ℕ) :
    Measurable (normalizedEventSuffix (S := S) n) := by
  apply measurable_pi_iff.mpr
  intro j
  cases j with
  | zero => exact measurable_const.prodMk (measurable_pi_apply n).snd
  | succ j => exact measurable_pi_apply (n + j + 1)

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem futureCylinderWeight_normalizedSuffix (n k : ℕ)
    (f : ℕ → ℝ × S → ℝ≥0∞) (w : ℕ → ℝ × S) :
    futureCylinderWeight 0 k f (normalizedEventSuffix n w) =
      futureCylinderWeight n k f w := by
  simp only [futureCylinderWeight, Nat.zero_add, normalizedEventSuffix]

end
end CTMCHeredity20261019

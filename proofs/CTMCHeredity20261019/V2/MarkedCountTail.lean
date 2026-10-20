module

public import proofs.HybridCTMCInfrastructure.TimedHistoryLaw
public import proofs.CTMCHeredity20261019.CF3MarkedKernel
public import proofs.CTMCHeredity20261019.V2.RawOperated

@[expose] public section

/-!
# Actual marked operation counts and their exponential tails

The clock/history Poisson identity is the sealed theorem for the constructed
`eventLaw`.  The multiplicative finite-history bound below is proved by the
actual finite kernel recursion, then mixed with that proved clock law.  No
compensator identity or Poisson domination is assumed.

The count drops the coordinate-zero sentinel and reads only `timedHistory T`.
For CF3, every `some (Sum.inr ...)` label is an actual complete division,
including null physical updates.  Idle and chemical labels contribute zero.
Unexecuted auxiliary future tails never enter the count.  Natural q/nd resets
do not reset or allocate these gross counts: operated histories sum the actual
executed marked-prefix count of each segment.
-/

namespace CTMCHeredity20261019.V2.MarkedCountTail

open MeasureTheory ProbabilityTheory HybridCTMC HybridCTMC.Kernel
open scoped BigOperators NNReal ENNReal Classical
noncomputable section

section FiniteHistory

variable {S : Type*} [Fintype S]

def wholeWeight (f : S → ℝ≥0∞) : List S → ℝ≥0∞
  | [] => 1
  | y :: ys => f y * wholeWeight f ys

def tailWeight (f : S → ℝ≥0∞) (ys : List S) : ℝ≥0∞ := wholeWeight f ys.tail

def countAll (P : S → Prop) : List S → ℕ
  | [] => 0
  | y :: ys => (if P y then 1 else 0) + countAll P ys

omit [Fintype S] in
theorem countAll_append (P : S → Prop) (xs ys : List S) :
    countAll P (xs ++ ys) = countAll P xs + countAll P ys := by
  induction xs with
  | nil => simp [countAll]
  | cons x xs ih => simp only [List.cons_append, countAll, ih, Nat.add_assoc]

omit [Fintype S] in
theorem countTail_le_append (P : S → Prop) (xs ys : List S) (hx : xs ≠ []) :
    countAll P xs.tail ≤ countAll P (xs ++ ys).tail := by
  cases xs with
  | nil => exact False.elim (hx rfl)
  | cons x xs => simp only [List.cons_append, List.tail_cons, countAll_append]; omega

omit [Fintype S] in
theorem eventPrefix_count_mono (P : S → Prop) (w : ℕ → ℝ × S) :
    Monotone (fun n => countAll P (statePrefix n w).tail) := by
  apply monotone_nat_of_le_succ
  intro n
  have hn : statePrefix n w ≠ [] := by
    intro he
    have hl := congrArg List.length he
    simp [statePrefix] at hl
  rw [statePrefix_succ]
  exact countTail_le_append P _ _ hn

theorem nnReward_mono {A : Type*} (p : PMF A) {f g : A → ℝ≥0∞}
    (h : ∀ x, f x ≤ g x) : nnReward p f ≤ nnReward p g :=
  ENNReal.tsum_le_tsum fun x => mul_le_mul_right (h x) (p x)

theorem nnReward_const_mul {A : Type*} (p : PMF A) (c : ℝ≥0∞) (f : A → ℝ≥0∞) :
    nnReward p (fun x => c * f x) = c * nnReward p f := by
  unfold nnReward
  calc
    _ = ∑' x, c * (p x * f x) := by
      apply tsum_congr
      intro x
      dsimp only
      ac_rfl
    _ = _ := ENNReal.tsum_mul_left

theorem nnReward_mul_const {A : Type*} (p : PMF A) (f : A → ℝ≥0∞) (c : ℝ≥0∞) :
    nnReward p (fun x => f x * c) = nnReward p f * c := by
  unfold nnReward
  simp only [← mul_assoc, ENNReal.tsum_mul_right]

theorem pmf_nnReward_ofReal (K : HybridCTMC.Kernel S) (f : S → ℝ)
    (hf : ∀ y, 0 ≤ f y) (x : S) :
    nnReward (K.pmf x) (fun y => ENNReal.ofReal (f y)) = ENNReal.ofReal (K.expect f x) := by
  rw [nnReward, tsum_fintype, Kernel.expect,
    ENNReal.ofReal_sum_of_nonneg (fun y _ => mul_nonneg (K.nonneg x y) (hf y))]
  apply Finset.sum_congr rfl
  intro y _
  rw [ENNReal.ofReal_mul (K.nonneg x y)]
  rfl

/-- Multiplicative finite-path estimate derived from the actual skeleton PMF. -/
theorem trajectory_wholeWeight_le (K : HybridCTMC.Kernel S)
    (f : S → ℝ≥0∞) (a : ℝ≥0∞) (hloc : ∀ x, nnReward (K.pmf x) f ≤ a)
    (n : ℕ) (x : S) :
    nnReward (K.trajectory n x) (wholeWeight f) ≤ f x * a ^ n := by
  induction n generalizing x with
  | zero => simp [Kernel.trajectory, nnReward_pure, wholeWeight]
  | succ n ih =>
      rw [Kernel.trajectory, nnReward_bind]
      simp only [nnReward_map, wholeWeight, nnReward_const_mul]
      calc
        _ ≤ f x * nnReward (K.pmf x) (fun y => f y * a ^ n) :=
          mul_le_mul_right (nnReward_mono (K.pmf x) (fun y => ih y)) (f x)
        _ = f x * (nnReward (K.pmf x) f * a ^ n) := by rw [nnReward_mul_const]
        _ ≤ f x * (a * a ^ n) :=
          mul_le_mul_right (mul_le_mul_left (hloc x) (a ^ n)) (f x)
        _ = f x * a ^ (n + 1) := by rw [pow_succ]; ac_rfl

/-- The initial coordinate contributes no factor. -/
theorem trajectory_tailWeight_le (K : HybridCTMC.Kernel S)
    (f : S → ℝ≥0∞) (a : ℝ≥0∞) (hloc : ∀ x, nnReward (K.pmf x) f ≤ a)
    (n : ℕ) (x : S) :
    nnReward (K.trajectory n x) (tailWeight f) ≤ a ^ n := by
  cases n with
  | zero => simp [Kernel.trajectory, nnReward_pure, tailWeight, wholeWeight]
  | succ n =>
      rw [Kernel.trajectory, nnReward_bind]
      simp only [nnReward_map, tailWeight, List.tail_cons]
      calc
        _ ≤ nnReward (K.pmf x) (fun y => f y * a ^ n) :=
          nnReward_mono (K.pmf x) (trajectory_wholeWeight_le K f a hloc n)
        _ = nnReward (K.pmf x) f * a ^ n := nnReward_mul_const _ _ _
        _ ≤ a * a ^ n := mul_le_mul_left (hloc x) (a ^ n)
        _ = a ^ (n + 1) := by rw [pow_succ]; ac_rfl

def tilt (P : S → Prop) (θ : ℝ) (y : S) : ℝ := if P y then Real.exp θ else 1

omit [Fintype S] in
theorem tilt_nonneg (P : S → Prop) (θ : ℝ) (y : S) : 0 ≤ tilt P θ y := by
  unfold tilt
  split_ifs <;> positivity

omit [Fintype S] in
theorem wholeWeight_tilt (P : S → Prop) (θ : ℝ) (ys : List S) :
    wholeWeight (fun y => ENNReal.ofReal (tilt P θ y)) ys =
      ENNReal.ofReal (Real.exp (θ * (countAll P ys : ℝ))) := by
  induction ys with
  | nil => simp [wholeWeight, countAll]
  | cons y ys ih =>
      change ENNReal.ofReal (tilt P θ y) *
        wholeWeight (fun y => ENNReal.ofReal (tilt P θ y)) ys =
          ENNReal.ofReal (Real.exp (θ *
            (((if P y then 1 else 0) + countAll P ys : ℕ) : ℝ)))
      rw [ih]
      by_cases hy : P y
      · simp only [tilt, ite_eq_left hy, Nat.cast_add, Nat.cast_one]
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
        congr 2
        ring
      · simp only [tilt, ite_eq_right hy, ENNReal.ofReal_one, one_mul, zero_add]

theorem expect_tilt (K : HybridCTMC.Kernel S) (P : S → Prop) (θ : ℝ) (x : S) :
    K.expect (tilt P θ) x = 1 + (Real.exp θ - 1) * K.event P x := by
  have he : tilt P θ = fun y => 1 + (Real.exp θ - 1) * (if P y then 1 else 0) := by
    funext y
    by_cases hy : P y <;> simp [tilt, hy]
  rw [he, Kernel.expect_add, Kernel.expect_const, Kernel.expect_scale]
  rfl

theorem poissonTrajectory_tailWeight_le (K : HybridCTMC.Kernel S)
    (f : S → ℝ≥0∞) {a : ℝ} (ha : 0 ≤ a)
    (hloc : ∀ x, nnReward (K.pmf x) f ≤ ENNReal.ofReal a) (r : ℝ≥0) (x : S) :
    nnReward (K.poissonTrajectory r x) (tailWeight f) ≤
      ENNReal.ofReal (Real.exp ((r : ℝ) * (a - 1))) := by
  rw [Kernel.poissonTrajectory, nnReward_bind]
  have hpmf (n : ℕ) : (poissonMeasure r).toPMF n = ENNReal.ofReal (poissonWeight r n) := by
    calc
      _ = poissonMeasure r {n} := (poissonMeasure r).toPMF_apply n
      _ = _ := poissonMeasure_singleton r n
  calc
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (poissonWeight r n) * (ENNReal.ofReal a) ^ n := by
      apply ENNReal.tsum_le_tsum
      intro n
      rw [hpmf]
      exact mul_le_mul_right (trajectory_tailWeight_le K f _ hloc n x) _
    _ = ∑' n : ℕ, ENNReal.ofReal (poissonWeight r n * a ^ n) := by
      apply tsum_congr
      intro n
      rw [ENNReal.ofReal_mul (poissonWeight_nonneg r n), ENNReal.ofReal_pow ha]
    _ = _ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg
        (fun n => mul_nonneg (poissonWeight_nonneg r n) (pow_nonneg ha n))
        (poisson_geometric_sum r a).summable, (poisson_geometric_sum r a).tsum_eq]

end FiniteHistory

section ActualTimedLaw

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- Count only retained positive-index states in the actually executed history. -/
def selectedCount (P : S → Prop) (T : ℝ) (w : ℕ → ℝ × S) : ℕ :=
  countAll P (timedHistory T w).tail

theorem measurable_selectedCount (P : S → Prop) (T : ℝ) : Measurable (selectedCount P T) :=
  measurable_timedHistory_observable T (fun ys => countAll P ys.tail)

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- Physical-time monotonicity uses an actual crossing, rather than declaring
the source clock index monotone on arbitrary pathological infinite paths. -/
theorem selectedCount_mono_of_crosses (P : S → Prop) (w : ℕ → ℝ × S)
    {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (hcross : ∃ n : ℕ, T < arrivalTime n w) :
    selectedCount P t w ≤ selectedCount P T w := by
  have hsmall : ∃ n : ℕ, t < arrivalTime n w := by
    obtain ⟨n, hn⟩ := hcross
    exact ⟨n, htT.trans_lt hn⟩
  have hs := clockIndex_segment ht w hsmall
  have hS := clockIndex_segment (ht.trans htT) w hcross
  have hi : clockIndex t w ≤ clockIndex T w := by
    by_contra h
    have hl : clockIndex T w < clockIndex t w := Nat.lt_of_not_ge h
    have ha := arrivalTime_mono w (show clockIndex T w + 1 ≤ clockIndex t w by omega)
    linarith [hs.1, hS.2]
  exact eventPrefix_count_mono P w hi

theorem ae_selectedCount_mono [StandardBorelSpace S] (K : HybridCTMC.Kernel S)
    {Lam : ℝ} (hLam : 0 < Lam) (x : S) (P : S → Prop) :
    ∀ᵐ w ∂K.eventLaw Lam hLam x, ∀ t T : ℝ, 0 ≤ t → t ≤ T →
      selectedCount P t w ≤ selectedCount P T w := by
  filter_upwards [CTMCHeredity20261019.ae_arrivals_unbounded K hLam x] with w hw
  intro t T ht htT
  exact selectedCount_mono_of_crosses P w ht htT (hw T)

/-- Actual physical-time MGF from a finite-kernel local probability bound. -/
theorem selectedCount_mgf (K : HybridCTMC.Kernel S) {Lam T θ r : ℝ}
    (hLam : 0 < Lam) (hT : 0 ≤ T) (hθ : 0 ≤ θ) (hr : 0 ≤ r)
    (P : S → Prop) (hloc : ∀ x, K.event P x ≤ r / Lam) (x : S) :
    (∫⁻ w, ENNReal.ofReal (Real.exp (θ * (selectedCount P T w : ℝ)))
      ∂K.eventLaw Lam hLam x) ≤
      ENNReal.ofReal (Real.exp (r * T * (Real.exp θ - 1))) := by
  let a : ℝ := 1 + (r / Lam) * (Real.exp θ - 1)
  have he : 0 ≤ Real.exp θ - 1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr hθ)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ht (s : S) : nnReward (K.pmf s) (fun y => ENNReal.ofReal (tilt P θ y)) ≤
      ENNReal.ofReal a := by
    rw [pmf_nnReward_ofReal K _ (tilt_nonneg P θ), expect_tilt]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ 1 + (Real.exp θ - 1) * (r / Lam) :=
        add_le_add_right (mul_le_mul_of_nonneg_left (hloc s) he) 1
      _ = a := by dsimp [a]; ring
  calc
    _ = ∫⁻ w, tailWeight (fun y => ENNReal.ofReal (tilt P θ y)) (timedHistory T w)
        ∂K.eventLaw Lam hLam x := by
      apply lintegral_congr
      intro w
      exact (wholeWeight_tilt P θ (timedHistory T w).tail).symm
    _ = nnReward (K.poissonTrajectory ⟨Lam * T, mul_nonneg hLam.le hT⟩ x)
        (tailWeight (fun y => ENNReal.ofReal (tilt P θ y))) :=
      K.timedHistory_reward hLam hT x _
    _ ≤ ENNReal.ofReal (Real.exp ((Lam * T) * (a - 1))) :=
      poissonTrajectory_tailWeight_le K _ ha ht _ x
    _ = _ := by
      congr 2
      dsimp [a]
      field_simp [hLam.ne']
      ring

end ActualTimedLaw

/-- Exponential Markov inequality in nonnegative-integral form. It needs no
unbounded signed expectation or integrability assumption. -/
theorem count_tail_of_mgf {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : Ω → ℕ) (hN : Measurable N) {θ A : ℝ} (hθ : 0 ≤ θ)
    (hmgf : (∫⁻ w, ENNReal.ofReal (Real.exp (θ * (N w : ℝ))) ∂μ) ≤
      ENNReal.ofReal (Real.exp A)) (k : ℕ) :
    μ {w | k ≤ N w} ≤ ENNReal.ofReal (Real.exp (A - θ * k)) := by
  have hs : MeasurableSet {w | k ≤ N w} := measurableSet_le measurable_const hN
  have hF : Measurable (fun w => ENNReal.ofReal (Real.exp (θ * (N w : ℝ)))) := by
    fun_prop
  calc
    _ = ∫⁻ w, {w | k ≤ N w}.indicator (fun _ => (1 : ℝ≥0∞)) w ∂μ :=
      (lintegral_indicator_one hs).symm
    _ ≤ ∫⁻ w, ENNReal.ofReal (Real.exp (-(θ * k))) *
        ENNReal.ofReal (Real.exp (θ * (N w : ℝ))) ∂μ := by
      apply lintegral_mono
      intro w
      by_cases hw : k ≤ N w
      · rw [Set.indicator_of_mem (s := {v : Ω | k ≤ N v}) (a := w) hw
          (fun _ : Ω => (1 : ℝ≥0∞))]
        change (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (-(θ * k))) *
          ENNReal.ofReal (Real.exp (θ * (N w : ℝ)))
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),
          ← Real.exp_add]
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        apply Real.one_le_exp_iff.mpr
        have hk : (k : ℝ) ≤ N w := by exact_mod_cast hw
        nlinarith
      · rw [Set.indicator_of_notMem (s := {v : Ω | k ≤ N v}) (a := w) hw
          (fun _ : Ω => (1 : ℝ≥0∞))]
        exact bot_le
    _ = ENNReal.ofReal (Real.exp (-(θ * k))) *
        ∫⁻ w, ENNReal.ofReal (Real.exp (θ * (N w : ℝ))) ∂μ :=
      lintegral_const_mul _ hF
    _ ≤ ENNReal.ofReal (Real.exp (-(θ * k))) * ENNReal.ofReal (Real.exp A) :=
      mul_le_mul_right hmgf _
    _ = _ := by rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]; congr 2; ring

section SourceDivisions

open FunctionalCapacity CF3Marked CF3RawPathLift

def isDivision {p : Par} : Option (Mark p) → Prop
  | some (Sum.inr _) => True
  | _ => False

def divisionState {p : Par} (z : CF3MarkedKernel.State p) : Prop := isDivision z.2

/-- Sum every actual division label, including split/victim refinements of
state-null updates. Chemistry and the explicit idle mark are excluded. -/
theorem division_event_eq {p : Par} (hp : p.Valid) (z : CF3MarkedKernel.State p) :
    (CF3MarkedKernel.kernel hp).event divisionState z =
      (∑ i, ∑ k, (cf3 p).rd (coreRepresent z.1 i) k) / cf3Rate p := by
  rw [Kernel.event, CF3MarkedKernel.kernel]
  let g : Option (Mark p) → ℝ := fun m => if isDivision m then 1 else 0
  change (MarkedKernel.kernel (coreChannels hp) (CF3MarkedKernel.rate_positive hp)
    (CF3MarkedKernel.core_channel_bound hp)).expect
      (fun y : CF3MarkedKernel.State p => g y.2) z = _
  rw [MarkedKernel.kernel_expect_mark]
  have hgNone : g none = 0 := by simp [g, isDivision]
  have hgChem (a : Fin p.M × Chem p.c) : g (some (Sum.inl a)) = 0 := by
    simp [g, isDivision]
  have hgDiv (a : Fin p.M × (Option (Fin p.c) × (Split p.c p.N × Fin p.M))) :
      g (some (Sum.inr a)) = 1 := by simp [g, isDivision]
  unfold MarkedUniformization.expect
  rw [Fintype.sum_option]
  simp only [hgNone, mul_zero, zero_add, Fintype.sum_sum_type, hgChem, hgDiv,
    Finset.sum_const_zero, mul_one]
  change (∑ d : Fin p.M × (Option (Fin p.c) × (Split p.c p.N × Fin p.M)),
    sourceIntensity p (coreRepresent z.1) (Sum.inr d) / cf3Rate p) = _
  have hi (i : Fin p.M) :
      (∑ u : Option (Fin p.c) × (Split p.c p.N × Fin p.M),
        sourceIntensity p (coreRepresent z.1) (Sum.inr (i, u)) / cf3Rate p) =
          (∑ k, (cf3 p).rd (coreRepresent z.1 i) k) / cf3Rate p := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.sum_div, divisionIntensity_sum hp]
  rw [Fintype.sum_prod_type]
  simp_rw [hi]
  rw [← Finset.sum_div]

/-- This source bound is independent of epsilon, raw ledgers and the old mark. -/
theorem division_event_le {p : Par} (hp : p.Valid) (z : CF3MarkedKernel.State p) :
    (CF3MarkedKernel.kernel hp).event divisionState z ≤
      ((p.M : ℝ) * (1 + p.c)) / cf3Rate p := by
  rw [division_event_eq hp]
  apply div_le_div_of_nonneg_right _ (CF3MarkedKernel.rate_positive hp).le
  calc
    _ ≤ ∑ _i : Fin p.M, (1 + (p.c : ℝ)) :=
      Finset.sum_le_sum fun i _ => cf3_rd_sum_le (coreRepresent z.1 i)
    _ = _ := by simp; ring

local instance (p : Par) : MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (CF3MarkedKernel.State p) :=
  ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (SourceState p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (SourceState p) := ⟨fun _ => trivial⟩

def divisionCount (p : Par) (T : ℝ) (w : MarkedPath p) : ℕ :=
  selectedCount divisionState T w

theorem measurable_divisionCount (p : Par) (T : ℝ) : Measurable (divisionCount p T) :=
  measurable_selectedCount divisionState T

/-- Source-instantiated physical division-count MGF, valid for both seed phases. -/
theorem divisionCount_mgf {p : Par} (hp : p.Valid) (hM : p.M = 4) (hc : p.c = 3)
    {T θ : ℝ} (hT : 0 ≤ T) (hθ : 0 ≤ θ) (x : CoreState p) (old : Option (Mark p)) :
    (∫⁻ w, ENNReal.ofReal (Real.exp (θ * (divisionCount p T w : ℝ)))
      ∂CF3MarkedKernel.eventLaw hp x old) ≤
      ENNReal.ofReal (Real.exp (16 * T * (Real.exp θ - 1))) := by
  apply selectedCount_mgf (CF3MarkedKernel.kernel hp)
    (CF3MarkedKernel.rate_positive hp) hT hθ (by norm_num) divisionState
  intro z
  have h := division_event_le hp z
  norm_num [hM, hc] at h
  exact h

/-- An elementary rational enclosure, proved from exp(-x) >= 1-x. -/
theorem exp_one_fifth_le : Real.exp ((1 : ℝ) / 5) ≤ ((20 : ℝ) / 19) ^ 4 := by
  have hs : Real.exp ((1 : ℝ) / 20) ≤ (20 : ℝ) / 19 := by
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-((1 : ℝ) / 20)))
      (Real.exp_nonneg ((1 : ℝ) / 20))
    have he : Real.exp ((1 : ℝ) / 20) * Real.exp (-((1 : ℝ) / 20)) = 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [he] at h
    nlinarith
  calc
    _ = (Real.exp ((1 : ℝ) / 20)) ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ _ := by gcongr

theorem division_exponent_le_neg_twenty :
    16 * (60 : ℝ) * (Real.exp ((1 : ℝ) / 5) - 1) - ((1 : ℝ) / 5) * 1200 ≤ -20 := by
  have h := exp_one_fifth_le
  norm_num at h ⊢
  nlinarith

/-- The stronger >=1200 tail bounds every attempted excess above 1200 as well. -/
theorem divisionCount_sixty_tail {p : Par} (hp : p.Valid) (hM : p.M = 4) (hc : p.c = 3)
    (x : CoreState p) (old : Option (Mark p)) :
    CF3MarkedKernel.eventLaw hp x old {w | 1200 ≤ divisionCount p 60 w} ≤
      ENNReal.ofReal (Real.exp (-20)) := by
  have ht := count_tail_of_mgf (CF3MarkedKernel.eventLaw hp x old)
    (divisionCount p 60) (measurable_divisionCount p 60) (by norm_num : 0 ≤ (1 : ℝ) / 5)
    (divisionCount_mgf hp hM hc (by norm_num : (0 : ℝ) ≤ 60)
      (by norm_num : 0 ≤ (1 : ℝ) / 5) x old) 1200
  exact ht.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr division_exponent_le_neg_twenty))

theorem canonical_seed_free_division_tail (x : CoreState canonicalSeedFreeCF3)
    (old : Option (Mark canonicalSeedFreeCF3)) :
    CF3MarkedKernel.eventLaw CF3MarkedKernel.canonical_valid x old
      {w | 1200 ≤ divisionCount canonicalSeedFreeCF3 60 w} ≤
      ENNReal.ofReal (Real.exp (-20)) :=
  divisionCount_sixty_tail CF3MarkedKernel.canonical_valid rfl rfl x old

theorem cf3_ae_divisionCount_mono {p : Par} (hp : p.Valid) (x : CoreState p)
    (old : Option (Mark p)) :
    ∀ᵐ w ∂CF3MarkedKernel.eventLaw hp x old, ∀ t T : ℝ, 0 ≤ t → t ≤ T →
      divisionCount p t w ≤ divisionCount p T w :=
  ae_selectedCount_mono (CF3MarkedKernel.kernel hp) (CF3MarkedKernel.rate_positive hp)
    (x, old) divisionState

/-- The terminal count controls every physical prefix through 60 on the actual
nonexplosive source law. This is a gross marked-count statement, not a ledger
reset or deterministic finite-stock coupling theorem. -/
theorem divisionCount_sixty_any_prefix_tail {p : Par} (hp : p.Valid)
    (hM : p.M = 4) (hc : p.c = 3) (x : CoreState p) (old : Option (Mark p)) :
    CF3MarkedKernel.eventLaw hp x old
      {w | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 60 ∧ 1200 ≤ divisionCount p t w} ≤
      ENNReal.ofReal (Real.exp (-20)) := by
  apply le_trans (measure_mono_ae (show ∀ᵐ w ∂CF3MarkedKernel.eventLaw hp x old,
    (∃ t : ℝ, 0 ≤ t ∧ t ≤ 60 ∧ 1200 ≤ divisionCount p t w) →
      1200 ≤ divisionCount p 60 w from by
      filter_upwards [cf3_ae_divisionCount_mono hp x old] with w hw
      rintro ⟨t, ht, htT, hn⟩
      exact hn.trans (hw t 60 ht htT)))
  exact divisionCount_sixty_tail hp hM hc x old

/-! Actual conditional operated-history composition. -/

def rawHistoryDivisionCount (p : Par) (T : ℝ) (n : ℕ)
    (h : RawOperated.History p n) : ℕ :=
  ∑ i : Fin n, divisionCount p T (h.1 i).1

theorem measurable_rawHistoryDivisionCount (p : Par) (T : ℝ) (n : ℕ) :
    Measurable (rawHistoryDivisionCount p T n) := by
  unfold rawHistoryDivisionCount
  apply Finset.measurable_sum
  intro i _
  exact (measurable_divisionCount p T).comp
    (measurable_fst.comp ((measurable_pi_apply i).comp measurable_fst))

theorem rawHistoryDivisionCount_prepend (p : Par) (T : ℝ) (n : ℕ)
    (s : RawOperated.Segment p) (h : RawOperated.History p n) :
    rawHistoryDivisionCount p T (n + 1) (Operated.prepend n (s, h)) =
      divisionCount p T s.1 + rawHistoryDivisionCount p T n h := by
  simp only [rawHistoryDivisionCount, Fin.sum_univ_succ, Operated.prepend,
    Fin.cons_zero, Fin.cons_succ]

theorem rawHistory_mgf_prepend (p : Par) (T θ : ℝ) (n : ℕ)
    (s : RawOperated.Segment p) (h : RawOperated.History p n) :
    ENNReal.ofReal (Real.exp (θ * (rawHistoryDivisionCount p T (n + 1)
      (Operated.prepend n (s, h)) : ℝ))) =
      ENNReal.ofReal (Real.exp (θ * (divisionCount p T s.1 : ℝ))) *
        ENNReal.ofReal (Real.exp (θ * (rawHistoryDivisionCount p T n h : ℝ))) := by
  rw [rawHistoryDivisionCount_prepend, Nat.cast_add, mul_add, Real.exp_add,
    ENNReal.ofReal_mul (Real.exp_nonneg _)]

/-- Actual segment-pair law; the observable reads only its executed marked
prefix.  The reset state and raw counters are arbitrary. -/
theorem segmentKernel_divisionCount_mgf {p : Par} (hp : p.Valid)
    (hM : p.M = 4) (hc : p.c = 3) {T θ : ℝ} (hT : 0 ≤ T) (hθ : 0 ≤ θ)
    (x : SourceState p) :
    (∫⁻ s, ENNReal.ofReal (Real.exp (θ * (divisionCount p T s.1 : ℝ)))
      ∂RawOperated.segmentKernel hp x) ≤
      ENNReal.ofReal (Real.exp (16 * T * (Real.exp θ - 1))) := by
  have hm : Measurable (fun s : RawOperated.Segment p =>
      ENNReal.ofReal (Real.exp (θ * (divisionCount p T s.1 : ℝ)))) :=
    ((measurable_of_countable (fun k : ℕ => ENNReal.ofReal (Real.exp (θ * k)))).comp
      (measurable_divisionCount p T)).comp measurable_fst
  change (∫⁻ s, ENNReal.ofReal (Real.exp (θ * (divisionCount p T s.1 : ℝ)))
    ∂(CF3MarkedKernel.eventLaw hp (coreProject x) none).map (RawOperated.rawPair p x)) ≤ _
  rw [lintegral_map hm (RawOperated.measurable_rawPair p x)]
  exact divisionCount_mgf hp hM hc hT hθ (coreProject x) none

/-- Product bound through the actual recursively conditioned joint operated
law.  Each tail begins at the sampled endpoint reset; no segment independence
or assumed conditional-count law is used. -/
theorem rawLaw_divisionCount_mgf_pow {p : Par} (hp : p.Valid)
    (hM : p.M = 4) (hc : p.c = 3) {T θ : ℝ} (hT : 0 ≤ T) (hθ : 0 ≤ θ)
    (n : ℕ) (x : SourceState p) :
    (∫⁻ h, ENNReal.ofReal (Real.exp (θ * (rawHistoryDivisionCount p T n h : ℝ)))
      ∂RawOperated.rawLaw hp T n x) ≤
      (ENNReal.ofReal (Real.exp (16 * T * (Real.exp θ - 1)))) ^ n := by
  let B : ℝ≥0∞ := ENNReal.ofReal (Real.exp (16 * T * (Real.exp θ - 1)))
  have hm (j : ℕ) : Measurable (fun h : RawOperated.History p j =>
      ENNReal.ofReal (Real.exp (θ * (rawHistoryDivisionCount p T j h : ℝ)))) :=
    (measurable_of_countable (fun k : ℕ => ENNReal.ofReal (Real.exp (θ * k)))).comp
      (measurable_rawHistoryDivisionCount p T j)
  have hs : Measurable (fun s : RawOperated.Segment p =>
      ENNReal.ofReal (Real.exp (θ * (divisionCount p T s.1 : ℝ)))) :=
    (measurable_of_countable (fun k : ℕ => ENNReal.ofReal (Real.exp (θ * k)))).comp
      ((measurable_divisionCount p T).comp measurable_fst)
  change _ ≤ B ^ n
  induction n generalizing x with
  | zero =>
      change (∫⁻ h, ENNReal.ofReal (Real.exp (θ * (rawHistoryDivisionCount p T 0 h : ℝ)))
        ∂Measure.dirac ((fun i : Fin 0 => Fin.elim0 i), x)) ≤ B ^ 0
      rw [lintegral_dirac' _ (hm 0)]
      simp [rawHistoryDivisionCount]
  | succ n ih =>
      rw [RawOperated.rawLaw_lintegral_step hp T n x _ (hm (n + 1))]
      calc
        _ = ∫⁻ s, ENNReal.ofReal (Real.exp (θ * (divisionCount p T s.1 : ℝ))) *
            (∫⁻ h, ENNReal.ofReal (Real.exp (θ * (rawHistoryDivisionCount p T n h : ℝ)))
              ∂RawOperated.rawLaw hp T n (RawOperated.nextState p T s))
              ∂RawOperated.segmentKernel hp x := by
          apply lintegral_congr
          intro s
          simp only [rawHistory_mgf_prepend]
          exact lintegral_const_mul _ (hm n)
        _ ≤ ∫⁻ s, ENNReal.ofReal (Real.exp (θ * (divisionCount p T s.1 : ℝ))) * B ^ n
            ∂RawOperated.segmentKernel hp x := by
          apply lintegral_mono
          intro s
          exact mul_le_mul_right (ih (RawOperated.nextState p T s)) _
        _ = (∫⁻ s, ENNReal.ofReal (Real.exp (θ * (divisionCount p T s.1 : ℝ)))
            ∂RawOperated.segmentKernel hp x) * B ^ n := lintegral_mul_const _ hs
        _ ≤ B * B ^ n := mul_le_mul_left
          (segmentKernel_divisionCount_mgf hp hM hc hT hθ x) (B ^ n)
        _ = B ^ (n + 1) := by rw [pow_succ]; ac_rfl

/-- Uniform all-block interface for two-source composition. -/
theorem rawLaw_divisionCount_mgf {p : Par} (hp : p.Valid)
    (hM : p.M = 4) (hc : p.c = 3) {T θ : ℝ} (hT : 0 ≤ T) (hθ : 0 ≤ θ)
    (n : ℕ) (x : SourceState p) :
    (∫⁻ h, ENNReal.ofReal (Real.exp (θ * (rawHistoryDivisionCount p T n h : ℝ)))
      ∂RawOperated.rawLaw hp T n x) ≤
      ENNReal.ofReal (Real.exp ((n : ℝ) * 16 * T * (Real.exp θ - 1))) := by
  have he : ENNReal.ofReal (Real.exp ((n : ℝ) * 16 * T * (Real.exp θ - 1))) =
      (ENNReal.ofReal (Real.exp (16 * T * (Real.exp θ - 1)))) ^ n := by
    rw [← ENNReal.ofReal_pow (Real.exp_nonneg _), ← Real.exp_nat_mul]
    congr 2
    ring
  rw [he]
  exact rawLaw_divisionCount_mgf_pow hp hM hc hT hθ n x

end SourceDivisions

end
end CTMCHeredity20261019.V2.MarkedCountTail

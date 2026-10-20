module

public import P161Formal.WeightedCountedPoisson
public import proofs.CTMCHeredity20261019.V2.RawOperated

/-! Retained endpoint witnesses through the actual operated-history law.
Counts read only positive-index executed marks. Core/fuel is not reset by
q bookkeeping, so the witness telescopes without a new local allocation. -/

@[expose] public section
namespace P161Formal
open MeasureTheory ProbabilityTheory HybridCTMC HybridCTMC.Kernel
open CTMCHeredity20261019 CF3Marked CF3RawPathLift V2
open CTMCHeredity20261019.V2.MarkedCountTail
open scoped BigOperators ENNReal Classical
noncomputable section

local instance weightedRawMeasurableSpace (p : FunctionalCapacity.Par) : MeasurableSpace (SourceState p) := ⊤
local instance weightedRawMeasurableSingleton (p : FunctionalCapacity.Par) : MeasurableSingletonClass (SourceState p) :=
  ⟨fun _ => trivial⟩
local instance weightedMarkedMeasurableSpace (p : FunctionalCapacity.Par) :
    MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance weightedMarkedMeasurableSingleton (p : FunctionalCapacity.Par) :
    MeasurableSingletonClass (CF3MarkedKernel.State p) := ⟨fun _ => trivial⟩

def rawHistorySelectedCount (p : FunctionalCapacity.Par) (P : CF3MarkedKernel.State p → Prop)
    (T : ℝ) (n : ℕ) (h : RawOperated.History p n) : ℕ :=
  ∑ i : Fin n, selectedCount P T (h.1 i).1

theorem measurable_rawHistorySelectedCount (p : FunctionalCapacity.Par)
    (P : CF3MarkedKernel.State p → Prop) (T : ℝ) (n : ℕ) :
    Measurable (rawHistorySelectedCount p P T n) := by
  unfold rawHistorySelectedCount
  apply Finset.measurable_sum
  intro i _
  exact (measurable_selectedCount P T).comp
    (measurable_fst.comp ((measurable_pi_apply i).comp measurable_fst))

theorem raw_history_selected_count_prepend (p : FunctionalCapacity.Par)
    (P : CF3MarkedKernel.State p → Prop) (T : ℝ) (n : ℕ)
    (s : RawOperated.Segment p) (h : RawOperated.History p n) :
    rawHistorySelectedCount p P T (n+1) (Operated.prepend n (s,h)) =
      selectedCount P T s.1+rawHistorySelectedCount p P T n h := by
  simp only [rawHistorySelectedCount,Fin.sum_univ_succ,Operated.prepend,Fin.cons_zero,Fin.cons_succ]

def rawHistoryWeightedReward (p : FunctionalCapacity.Par) (P : CF3MarkedKernel.State p → Prop)
    (T θ : ℝ) (U : CoreState p → ℝ) (n : ℕ) (h : RawOperated.History p n) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (θ*(rawHistorySelectedCount p P T n h : ℝ)))*
    ENNReal.ofReal (U (coreProject h.2))

theorem measurable_rawHistoryWeightedReward (p : FunctionalCapacity.Par)
    (P : CF3MarkedKernel.State p → Prop) (T θ : ℝ) (U : CoreState p → ℝ) (n : ℕ) :
    Measurable (rawHistoryWeightedReward p P T θ U n) :=
  ((measurable_of_countable (fun k : ℕ => ENNReal.ofReal (Real.exp (θ*k)))).comp
    (measurable_rawHistorySelectedCount p P T n)).mul
    ((measurable_of_countable (fun y : SourceState p => ENNReal.ofReal (U (coreProject y)))).comp measurable_snd)

theorem raw_history_weighted_reward_prepend (p : FunctionalCapacity.Par)
    (P : CF3MarkedKernel.State p → Prop) (T θ : ℝ) (U : CoreState p → ℝ) (n : ℕ)
    (s : RawOperated.Segment p) (h : RawOperated.History p n) :
    rawHistoryWeightedReward p P T θ U (n+1) (Operated.prepend n (s,h)) =
      ENNReal.ofReal (Real.exp (θ*(selectedCount P T s.1 : ℝ)))*
        rawHistoryWeightedReward p P T θ U n h := by
  unfold rawHistoryWeightedReward
  rw [raw_history_selected_count_prepend,Nat.cast_add,mul_add,Real.exp_add,
    ENNReal.ofReal_mul (Real.exp_nonneg _)]
  exact mul_assoc _ _ _

theorem raw_law_weighted_bound_pow {p : FunctionalCapacity.Par} (hp : p.Valid)
    (P : CF3MarkedKernel.State p → Prop) (T θ : ℝ) (U : CoreState p → ℝ) (B : ℝ≥0∞)
    (hsegment : ∀ x : SourceState p,
      (∫⁻ s, ENNReal.ofReal (Real.exp (θ*(selectedCount P T s.1 : ℝ)))*
        ENNReal.ofReal (U (coreProject (RawOperated.nextState p T s))) ∂RawOperated.segmentKernel hp x) ≤
          B*ENNReal.ofReal (U (coreProject x))) (n : ℕ) (x : SourceState p) :
    (∫⁻ h, rawHistoryWeightedReward p P T θ U n h ∂RawOperated.rawLaw hp T n x) ≤
      B^n*ENNReal.ofReal (U (coreProject x)) := by
  have hm (j : ℕ) := measurable_rawHistoryWeightedReward p P T θ U j
  have hs : Measurable (fun s : RawOperated.Segment p =>
      ENNReal.ofReal (Real.exp (θ*(selectedCount P T s.1 : ℝ)))*
        ENNReal.ofReal (U (coreProject (RawOperated.nextState p T s)))) :=
    ((measurable_of_countable (fun k : ℕ => ENNReal.ofReal (Real.exp (θ*k)))).comp
      ((measurable_selectedCount P T).comp measurable_fst)).mul
      ((measurable_of_countable (fun y : SourceState p => ENNReal.ofReal (U (coreProject y)))).comp
        (RawOperated.measurable_nextState p T))
  induction n generalizing x with
  | zero =>
    change (∫⁻ h, rawHistoryWeightedReward p P T θ U 0 h
      ∂Measure.dirac ((fun i : Fin 0 => Fin.elim0 i),x)) ≤ B^0*ENNReal.ofReal (U (coreProject x))
    rw [lintegral_dirac' _ (hm 0)]
    simp [rawHistoryWeightedReward,rawHistorySelectedCount]
  | succ n ih =>
    rw [RawOperated.rawLaw_lintegral_step hp T n x _ (hm (n+1))]
    calc
      _ = ∫⁻ s, ENNReal.ofReal (Real.exp (θ*(selectedCount P T s.1 : ℝ)))*
          (∫⁻ h, rawHistoryWeightedReward p P T θ U n h
            ∂RawOperated.rawLaw hp T n (RawOperated.nextState p T s))
          ∂RawOperated.segmentKernel hp x := by
        apply lintegral_congr
        intro s
        simp only [raw_history_weighted_reward_prepend]
        exact lintegral_const_mul _ (hm n)
      _ ≤ ∫⁻ s, ENNReal.ofReal (Real.exp (θ*(selectedCount P T s.1 : ℝ)))*
          (B^n*ENNReal.ofReal (U (coreProject (RawOperated.nextState p T s))))
          ∂RawOperated.segmentKernel hp x :=
        lintegral_mono (fun s => mul_le_mul_right (ih (RawOperated.nextState p T s)) _)
      _ = B^n*(∫⁻ s, ENNReal.ofReal (Real.exp (θ*(selectedCount P T s.1 : ℝ)))*
          ENNReal.ofReal (U (coreProject (RawOperated.nextState p T s)))
          ∂RawOperated.segmentKernel hp x) := by
        have he : (fun s : RawOperated.Segment p =>
            ENNReal.ofReal (Real.exp (θ*(selectedCount P T s.1 : ℝ)))*
              (B^n*ENNReal.ofReal (U (coreProject (RawOperated.nextState p T s))))) =
            (fun s => B^n*(ENNReal.ofReal (Real.exp (θ*(selectedCount P T s.1 : ℝ)))*
              ENNReal.ofReal (U (coreProject (RawOperated.nextState p T s))))) := by
          funext s
          ac_rfl
        rw [he]
        exact lintegral_const_mul _ hs
      _ ≤ B^n*(B*ENNReal.ofReal (U (coreProject x))) := mul_le_mul_right (hsegment x) (B^n)
      _ = B^(n+1)*ENNReal.ofReal (U (coreProject x)) := by rw [pow_succ]; ac_rfl

theorem source_reset_q_core {p : FunctionalCapacity.Par} (x : SourceState p) :
    coreProject (sourceResetQ (p := p) x) = coreProject x := rfl

theorem actual_segment_weighted_bound {p : FunctionalCapacity.Par} (hp : p.Valid)
    (P : CF3MarkedKernel.State p → Prop) (θ : ℝ) (U : CoreState p → ℝ)
    {T a : ℝ} (hT : 0 ≤ T) (ha : 0 ≤ a)
    (hloc : ∀ z : CF3MarkedKernel.State p,
      nnReward ((CF3MarkedKernel.kernel hp).pmf z)
        (fun y => ENNReal.ofReal (tilt P θ y)*ENNReal.ofReal (U y.1)) ≤
          ENNReal.ofReal a*ENNReal.ofReal (U z.1)) (x : SourceState p) :
    (∫⁻ s, ENNReal.ofReal (Real.exp (θ*(selectedCount P T s.1 : ℝ)))*
      ENNReal.ofReal (U (coreProject (RawOperated.nextState p T s))) ∂RawOperated.segmentKernel hp x) ≤
        ENNReal.ofReal (Real.exp (FunctionalCapacity.cf3Rate p*T*(a-1)))*
          ENNReal.ofReal (U (coreProject x)) := by
  have hm : Measurable (fun s : RawOperated.Segment p =>
      ENNReal.ofReal (Real.exp (θ*(selectedCount P T s.1 : ℝ)))*
        ENNReal.ofReal (U (coreProject (RawOperated.nextState p T s)))) :=
    ((measurable_of_countable (fun k : ℕ => ENNReal.ofReal (Real.exp (θ*k)))).comp
      ((measurable_selectedCount P T).comp measurable_fst)).mul
      ((measurable_of_countable (fun y : SourceState p => ENNReal.ofReal (U (coreProject y)))).comp
        (RawOperated.measurable_nextState p T))
  have ht := timed_weighted_count_moment (CF3MarkedKernel.kernel hp) P θ (fun z => U z.1)
    (CF3MarkedKernel.rate_positive hp) ha hT hloc (coreProject x,none)
  calc
    _ = ∫⁻ w, ENNReal.ofReal (Real.exp (θ*(selectedCount P T w : ℝ)))*
        ENNReal.ofReal (U (timedState T w).1) ∂CF3MarkedKernel.eventLaw hp (coreProject x) none := by
      change (∫⁻ s : RawOperated.Segment p,
        ENNReal.ofReal (Real.exp (θ*(selectedCount P T s.1 : ℝ)))*
          ENNReal.ofReal (U (coreProject (RawOperated.nextState p T s)))
        ∂(CF3MarkedKernel.eventLaw hp (coreProject x) none).map (RawOperated.rawPair p x)) = _
      rw [lintegral_map hm (RawOperated.measurable_rawPair p x)]
      apply lintegral_congr_ae
      filter_upwards [ae_rawSequence_timed_project hp x none] with w hw
      change ENNReal.ofReal (Real.exp (θ*(selectedCount P T w : ℝ)))*
          ENNReal.ofReal (U (coreProject (sourceResetQ (p := p) (timedState T (rawSequence p x w))))) = _
      rw [source_reset_q_core,hw T]
    _ ≤ _ := ht

theorem actual_raw_law_weighted_bound {p : FunctionalCapacity.Par} (hp : p.Valid)
    (P : CF3MarkedKernel.State p → Prop) (θ : ℝ) (U : CoreState p → ℝ)
    {T a : ℝ} (hT : 0 ≤ T) (ha : 0 ≤ a)
    (hloc : ∀ z : CF3MarkedKernel.State p,
      nnReward ((CF3MarkedKernel.kernel hp).pmf z)
        (fun y => ENNReal.ofReal (tilt P θ y)*ENNReal.ofReal (U y.1)) ≤
          ENNReal.ofReal a*ENNReal.ofReal (U z.1)) (n : ℕ) (x : SourceState p) :
    (∫⁻ h, rawHistoryWeightedReward p P T θ U n h ∂RawOperated.rawLaw hp T n x) ≤
      ENNReal.ofReal (Real.exp ((n : ℝ)*FunctionalCapacity.cf3Rate p*T*(a-1)))*
        ENNReal.ofReal (U (coreProject x)) := by
  have h := raw_law_weighted_bound_pow hp P T θ U
    (ENNReal.ofReal (Real.exp (FunctionalCapacity.cf3Rate p*T*(a-1))))
    (actual_segment_weighted_bound hp P θ U hT ha hloc) n x
  have he : (ENNReal.ofReal (Real.exp (FunctionalCapacity.cf3Rate p*T*(a-1))))^n =
      ENNReal.ofReal (Real.exp ((n : ℝ)*FunctionalCapacity.cf3Rate p*T*(a-1))) := by
    rw [←ENNReal.ofReal_pow (Real.exp_nonneg _),←Real.exp_nat_mul]
    congr 2
    ring
  simpa only [he] using h

end
end P161Formal

module

public import proofs.HybridCTMCInfrastructure.ClockInterpolation
public import proofs.HybridCTMCInfrastructure.ClockSupport
public import proofs.HybridCTMCInfrastructure.EventMaximal

@[expose] public section

/-! State and compensated-coordinate processes indexed by continuous time.
Nonexplosion of the actual clock law ensures that the crossing index exists
almost surely for each finite horizon. -/
namespace HybridCTMC
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical
noncomputable section
namespace Kernel
variable {S : Type*} [Fintype S]

def clockIndex (t : ℝ) (w : ℕ → ℝ × S) : ℕ :=
  if h : ∃ n, t < arrivalTime n w then Nat.find h-1 else 0

def timedState (t : ℝ) (w : ℕ → ℝ × S) : S := (w (clockIndex t w)).2

def timedCompensated (K : HybridCTMC.Kernel S) (Λ : ℝ) (f : S → ℝ)
    (t : ℝ) (w : ℕ → ℝ × S) : ℝ :=
  K.eventCompensator Λ f (clockIndex t w) w-
    Λ*(K.expect f (timedState t w)-f (timedState t w))*(t-arrivalTime (clockIndex t w) w)

omit [Fintype S] in
theorem clockIndex_segment {t : ℝ} (ht : 0 ≤ t) (w : ℕ → ℝ × S)
    (hex : ∃ n, t < arrivalTime n w) :
    arrivalTime (clockIndex t w) w ≤ t ∧ t < arrivalTime (clockIndex t w+1) w := by
  have hmpos : 0 < Nat.find hex := by
    by_contra h
    have he : Nat.find hex = 0 := Nat.eq_zero_of_not_pos h
    have hh := Nat.find_spec hex
    rw [he] at hh
    simp [arrivalTime, not_lt.mpr ht] at hh
  have hs : Nat.find hex-1+1 = Nat.find hex := Nat.sub_add_cancel hmpos
  rw [clockIndex, dite_eq_left hex]
  constructor
  · exact le_of_not_gt (Nat.find_min hex (Nat.sub_lt hmpos (by decide)))
  · rw [hs]
    exact Nat.find_spec hex

theorem timedCompensated_segment_bound (K : HybridCTMC.Kernel S) (Λ : ℝ) (f : S → ℝ)
    {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (w : ℕ → ℝ × S)
    (hex : ∃ n, T < arrivalTime n w) :
    |K.timedCompensated Λ f t w| ≤
      max |K.horizonSum Λ f T (clockIndex t w) w|
        |K.horizonSum Λ f T (clockIndex t w+1) w|+
          |f (w (clockIndex t w+1)).2-f (w (clockIndex t w)).2| := by
  obtain ⟨m, hm⟩ := hex
  have hs := clockIndex_segment ht w ⟨m, htT.trans_lt hm⟩
  have hsuc : arrivalTime (clockIndex t w+1) w =
      arrivalTime (clockIndex t w) w+max 0 (w (clockIndex t w+1)).1 := by
    simp [arrivalTime, Finset.sum_range_succ]
  have hH : 0 < (w (clockIndex t w+1)).1 := by
    have hm : 0 < max 0 (w (clockIndex t w+1)).1 := by linarith [hs.1, hs.2]
    simpa only [lt_max_iff, lt_self_iff_false, false_or] using hm
  have hu : t-arrivalTime (clockIndex t w) w ≤ (w (clockIndex t w+1)).1 := by
    rw [max_eq_right hH.le] at hsuc
    linarith [hs.2]
  exact K.clock_segment_bound Λ f T (clockIndex t w) w (hs.1.trans htT) hH
    (sub_nonneg.mpr hs.1) hu

variable [MeasurableSpace S] [MeasurableSingletonClass S] [StandardBorelSpace S]

omit [Fintype S] [MeasurableSingletonClass S] [StandardBorelSpace S] in
theorem measurable_clockIndex (t : ℝ) : Measurable (clockIndex (S := S) t) := by
  let p : (ℕ → ℝ × S) → ℕ → Prop := fun w n =>
    t < arrivalTime n w ∨ ¬∃ m, t < arrivalTime m w
  have hp : ∀ w, ∃ n, p w n := by
    intro w
    by_cases h : ∃ n, t < arrivalTime n w
    · obtain ⟨n, hn⟩ := h
      exact ⟨n, Or.inl hn⟩
    · exact ⟨0, Or.inr h⟩
  have hm (n : ℕ) : MeasurableSet {w : ℕ → ℝ × S | t < arrivalTime n w} :=
    measurableSet_lt measurable_const ((measurable_arrivalTime n).mono (Filtration.piLE.le n) le_rfl)
  have hex : MeasurableSet {w : ℕ → ℝ × S | ∃ n, t < arrivalTime n w} := by
    simp only [ofPred_exists]
    exact MeasurableSet.iUnion hm
  have hpm (n : ℕ) : MeasurableSet {w | p w n} := (hm n).union hex.compl
  have he : clockIndex (S := S) t = fun w => Nat.find (hp w)-1 := by
    funext w
    by_cases h : ∃ n, t < arrivalTime n w
    · rw [clockIndex, dite_eq_left h]
      congr 1
      exact Nat.find_congr' (by simp [p, h])
    · rw [clockIndex, dite_eq_right h]
      have hz : Nat.find (hp w) = 0 := (Nat.find_eq_zero _).mpr (Or.inr h)
      simp [hz]
  rw [he]
  exact (measurable_of_countable (fun n : ℕ => n-1)).comp (measurable_find hp hpm)

omit [Fintype S] [MeasurableSingletonClass S] [StandardBorelSpace S] in
theorem measurable_timedState (t : ℝ) : Measurable (timedState (S := S) t) := by
  have he : Measurable (fun z : (ℕ → ℝ × S) × ℕ => z.1 z.2) :=
    measurable_from_prod_countable_left (fun n => measurable_pi_apply n)
  exact (he.comp (measurable_id.prodMk (measurable_clockIndex t))).snd

omit [StandardBorelSpace S] in
theorem measurable_timedCompensated (K : HybridCTMC.Kernel S) (Λ : ℝ) (f : S → ℝ) (t : ℝ) :
    Measurable (K.timedCompensated Λ f t) := by
  have hi := measurable_id.prodMk (measurable_clockIndex (S := S) t)
  have hM : Measurable (fun z : (ℕ → ℝ × S) × ℕ => K.eventCompensator Λ f z.2 z.1) :=
    measurable_from_prod_countable_left (fun n =>
      (K.stronglyAdapted_eventCompensator Λ f n).measurable.mono (Filtration.piLE.le n) le_rfl)
  have hA : Measurable (fun z : (ℕ → ℝ × S) × ℕ => arrivalTime z.2 z.1) :=
    measurable_from_prod_countable_left (fun n =>
      (measurable_arrivalTime n).mono (Filtration.piLE.le n) le_rfl)
  have hf := (measurable_of_countable f).comp (measurable_timedState (S := S) t)
  have hK := (measurable_of_countable (K.expect f)).comp (measurable_timedState (S := S) t)
  exact (hM.comp hi).sub (((hK.sub hf).const_mul Λ).mul (measurable_const.sub (hA.comp hi)))

theorem timedCompensated_maximal (K : HybridCTMC.Kernel S) {Λ θ : ℝ}
    (hΛ : 0 < Λ) (hθ : 0 < θ) (f : S → ℝ) (x : S) (T : ℝ) {v J η : ℝ}
    (hv0 : 0 ≤ v) (hη : J < η)
    (hv : ∀ s, K.expect (fun y => (f y-f s)^2) s ≤ v)
    (hj : ∀ s y, 0 < K.weight s y → |f y-f s| ≤ J) :
    K.eventLaw Λ hΛ x {w | ∃ t, 0 ≤ t ∧ t ≤ T ∧ η ≤ |K.timedCompensated Λ f t w|} ≤
      ENNReal.ofReal ((v*(Real.exp (θ*T)*(Λ+θ)/θ))/(η-J)^2) := by
  have ha := K.ae_arrival_crosses hΛ x T
  have hjump := K.ae_event_jump hΛ f x hj
  have hsub : ∀ᵐ w ∂K.eventLaw Λ hΛ x,
      (∃ t, 0 ≤ t ∧ t ≤ T ∧ η ≤ |K.timedCompensated Λ f t w|) →
        ∃ n, η-J ≤ |K.horizonSum Λ f T n w| := by
    filter_upwards [ha, hjump] with w hw hJ
    rintro ⟨t, ht, htT, hbad⟩
    have hb := K.timedCompensated_segment_bound Λ f ht htT w hw
    have hmax : η-J ≤ max |K.horizonSum Λ f T (clockIndex t w) w|
        |K.horizonSum Λ f T (clockIndex t w+1) w| := by linarith [hJ (clockIndex t w)]
    rcases le_max_iff.mp hmax with h | h
    · exact ⟨clockIndex t w, h⟩
    · exact ⟨clockIndex t w+1, h⟩
  exact (measure_mono_ae hsub).trans (K.horizon_maximal hΛ hθ f x T hv0 (sub_pos.mpr hη) hv)
end Kernel
end
end HybridCTMC

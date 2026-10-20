module

public import P161Formal.CountedLiveHistory
public import proofs.HybridCTMCInfrastructure.TimedHistoryLaw

/-! Poisson mixing and physical-time interpretation of counted live histories.
The kernel and clock law are the actual constructed ones. Only source-local
one-step witness inequalities remain parameters of this reusable theorem. -/

@[expose] public section
namespace P161Formal
open MeasureTheory ProbabilityTheory HybridCTMC HybridCTMC.Kernel
open scoped BigOperators NNReal ENNReal Classical
noncomputable section

variable {S : Type*} [Fintype S]

theorem poisson_counted_live_bound (K : HybridCTMC.Kernel S)
    (live P : S → Prop) (U : S → ℝ) (a b : ℝ)
    (hU : ∀ x, 0 ≤ U x) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ x, live x →
      K.expect (fun y => if live y ∧ ¬P y then U y else 0) x ≤ a*U x)
    (hB : ∀ x, live x →
      K.expect (fun y => if live y ∧ P y then U y else 0) x ≤ b*U x)
    (r : ℝ≥0) (j : ℕ) (x : S) :
    nnReward (K.poissonTrajectory r x) (tailLiveReward live P U j) ≤
      ENNReal.ofReal ((Real.exp ((r : ℝ)*(a-1))*((r : ℝ)*b)^j/j.factorial)*U x) := by
  have hpmf (n : ℕ) : (poissonMeasure r).toPMF n = ENNReal.ofReal (poissonWeight r n) := by
    calc
      _ = poissonMeasure r {n} := (poissonMeasure r).toPMF_apply n
      _ = _ := poissonMeasure_singleton r n
  have hs := (poisson_word_hasSum (r : ℝ) a b j).mul_right (U x)
  rw [Kernel.poissonTrajectory,nnReward_bind]
  calc
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (poissonWeight r n)*
        ENNReal.ofReal (binomialWordCoefficient n j a b*U x) := by
      apply ENNReal.tsum_le_tsum
      intro n
      rw [hpmf]
      apply mul_le_mul_right
      have h := trajectory_counted_live_bound K live P U a b hU ha hb hA hB n j x
      exact h.trans (ENNReal.ofReal_le_ofReal (by
        split_ifs
        · exact le_rfl
        · exact mul_nonneg (word_coefficient_nonnegative n j a b ha hb) (hU x)))
    _ = ∑' n : ℕ, ENNReal.ofReal (poissonWordTerm (r : ℝ) a b j n*U x) := by
      apply tsum_congr
      intro n
      rw [← ENNReal.ofReal_mul (poissonWeight_nonneg r n)]
      congr 1
      unfold poissonWeight poissonWordTerm
      ring
    _ = _ := by
      have hn (n : ℕ) : 0 ≤ poissonWordTerm (r : ℝ) a b j n*U x := by
        unfold poissonWordTerm
        exact mul_nonneg (mul_nonneg (by positivity)
          (word_coefficient_nonnegative n j a b ha hb)) (hU x)
      rw [← ENNReal.ofReal_tsum_of_nonneg hn hs.summable,hs.tsum_eq]

omit [Fintype S] in
theorem history_terminal_barrier (live : S → Prop) (U : S → ℝ)
    (hU : ∀ x, live x → 1 ≤ U x) (xs : List S) (hne : xs ≠ [])
    (hlive : ∀ x ∈ xs, live x) : 1 ≤ historyTerminal U xs := by
  induction xs with
  | nil => exact (hne rfl).elim
  | cons x xs ih =>
      cases xs with
      | nil =>
          change (1 : ℝ≥0∞) ≤ ENNReal.ofReal (U x)
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (hU x (hlive x (by simp)))
      | cons y ys =>
          exact ih (by simp) (fun z hz => hlive z (List.mem_cons_of_mem x hz))

def countedLiveEvent (live P : S → Prop) (K : ℕ) (xs : List S) : Prop :=
  xs ≠ [] ∧ (∀ x ∈ xs, live x) ∧ historyMarkCount P xs.tail < K

omit [Fintype S] in
theorem counted_live_event_reward (live P : S → Prop) (U : S → ℝ)
    (hU : ∀ x, live x → 1 ≤ U x) (K : ℕ) (xs : List S) :
    (if countedLiveEvent live P K xs then (1 : ℝ≥0∞) else 0) ≤
      ∑ j ∈ Finset.range K, tailLiveReward live P U j xs := by
  by_cases hx : countedLiveEvent live P K xs
  · simp only [hx,ite_true]
    have hm : historyMarkCount P xs.tail ∈ Finset.range K := Finset.mem_range.mpr hx.2.2
    calc
      _ ≤ historyTerminal U xs := history_terminal_barrier live U hU xs hx.1 hx.2.1
      _ = tailLiveReward live P U (historyMarkCount P xs.tail) xs := by
        have hp : (∀ z ∈ xs, live z) ∧ historyMarkCount P xs.tail = historyMarkCount P xs.tail :=
          ⟨hx.2.1,rfl⟩
        unfold tailLiveReward
        rw [ite_eq_left hp]
      _ ≤ _ := Finset.single_le_sum (s := Finset.range K)
        (f := fun j : ℕ => tailLiveReward live P U j xs)
        (fun j _ => (show (0 : ℝ≥0∞) ≤ tailLiveReward live P U j xs from bot_le)) hm
  · simp [hx]

theorem nnReward_finset_sum {A I : Type*} (p : PMF A) (s : Finset I)
    (f : I → A → ℝ≥0∞) :
    nnReward p (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, nnReward p (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [nnReward]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi,nnReward,mul_add,ENNReal.tsum_add]
      exact congrArg (fun z => (∑' x, p x*f i x)+z) ih

theorem poisson_counted_live_event_bound (K : HybridCTMC.Kernel S)
    (live P : S → Prop) (U : S → ℝ) (a b : ℝ)
    (hU : ∀ x, 0 ≤ U x) (hbarrier : ∀ x, live x → 1 ≤ U x)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ x, live x →
      K.expect (fun y => if live y ∧ ¬P y then U y else 0) x ≤ a*U x)
    (hB : ∀ x, live x →
      K.expect (fun y => if live y ∧ P y then U y else 0) x ≤ b*U x)
    (r : ℝ≥0) (J : ℕ) (x : S) :
    mass (K.poissonTrajectory r x) (countedLiveEvent live P J) ≤
      ENNReal.ofReal ((Real.exp ((r : ℝ)*(a-1))*
        (∑ j ∈ Finset.range J, ((r : ℝ)*b)^j/j.factorial))*U x) := by
  have hUx := hU x
  have hmass : mass (K.poissonTrajectory r x) (countedLiveEvent live P J) =
      nnReward (K.poissonTrajectory r x)
        (fun xs => if countedLiveEvent live P J xs then 1 else 0) := by
    simp [mass,nnReward,mul_ite]
  rw [hmass]
  calc
    _ ≤ nnReward (K.poissonTrajectory r x)
        (fun xs => ∑ j ∈ Finset.range J, tailLiveReward live P U j xs) :=
      nnReward_pointwise_le _ _ _ (counted_live_event_reward live P U hbarrier J)
    _ = ∑ j ∈ Finset.range J,
        nnReward (K.poissonTrajectory r x) (tailLiveReward live P U j) :=
      nnReward_finset_sum _ _ _
    _ ≤ ∑ j ∈ Finset.range J,
        ENNReal.ofReal ((Real.exp ((r : ℝ)*(a-1))*((r : ℝ)*b)^j/j.factorial)*U x) :=
      Finset.sum_le_sum (fun j _ => poisson_counted_live_bound K live P U a b hU ha hb hA hB r j x)
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
      congr 1
      rw [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring

variable [MeasurableSpace S] [MeasurableSingletonClass S]

theorem timed_counted_live_event_bound (K : HybridCTMC.Kernel S)
    (live P : S → Prop) (U : S → ℝ) (a b : ℝ)
    (hU : ∀ x, 0 ≤ U x) (hbarrier : ∀ x, live x → 1 ≤ U x)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ x, live x →
      K.expect (fun y => if live y ∧ ¬P y then U y else 0) x ≤ a*U x)
    (hB : ∀ x, live x →
      K.expect (fun y => if live y ∧ P y then U y else 0) x ≤ b*U x)
    {Lam T : ℝ} (hLam : 0 < Lam) (hT : 0 ≤ T) (J : ℕ) (x : S) :
    K.eventLaw Lam hLam x
      {w | countedLiveEvent live P J (timedHistory T w)} ≤
      ENNReal.ofReal ((Real.exp (Lam*T*(a-1))*
        (∑ j ∈ Finset.range J, (Lam*T*b)^j/j.factorial))*U x) := by
  rw [K.timedHistory_event hLam hT]
  exact poisson_counted_live_event_bound K live P U a b hU hbarrier ha hb hA hB
    ⟨Lam*T,mul_nonneg hLam.le hT⟩ J x

end
end P161Formal

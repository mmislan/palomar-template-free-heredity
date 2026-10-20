module

public import P161Formal.PoissonWords
public import proofs.HybridCTMCInfrastructure.SkeletonPaths
public import proofs.HybridCTMCInfrastructure.PrefixReward

/-! Counted live histories of the actual finite skeleton. The first state is
an initial sentinel: only the tail contributes actual marks. Every visited
state is tested for liveness, including the initial and terminal states. -/

@[expose] public section
namespace P161Formal
open MeasureTheory ProbabilityTheory HybridCTMC HybridCTMC.Kernel
open scoped BigOperators ENNReal Classical
noncomputable section

variable {S : Type*}

def historyMarkCount (P : S → Prop) : List S → ℕ
  | [] => 0
  | x :: xs => (if P x then 1 else 0) + historyMarkCount P xs

def historyTerminal (U : S → ℝ) : List S → ℝ≥0∞
  | [] => 0
  | [x] => ENNReal.ofReal (U x)
  | _ :: y :: ys => historyTerminal U (y :: ys)

def wholeLiveReward (live P : S → Prop) (U : S → ℝ) (j : ℕ)
    (xs : List S) : ℝ≥0∞ :=
  if (∀ x ∈ xs, live x) ∧ historyMarkCount P xs = j then historyTerminal U xs else 0

def tailLiveReward (live P : S → Prop) (U : S → ℝ) (j : ℕ)
    (xs : List S) : ℝ≥0∞ :=
  if (∀ x ∈ xs, live x) ∧ historyMarkCount P xs.tail = j then historyTerminal U xs else 0

theorem tail_live_reward_cons (live P : S → Prop) (U : S → ℝ) (j : ℕ)
    (x y : S) (ys : List S) :
    tailLiveReward live P U j (x :: y :: ys) =
      if live x then wholeLiveReward live P U j (y :: ys) else 0 := by
  by_cases hx : live x <;>
    simp [tailLiveReward,wholeLiveReward,historyTerminal,hx]

theorem whole_live_reward_zero (live P : S → Prop) (U : S → ℝ)
    (x : S) (xs : List S) :
    wholeLiveReward live P U 0 (x :: xs) =
      if P x then 0 else tailLiveReward live P U 0 (x :: xs) := by
  by_cases hx : P x <;>
    simp [wholeLiveReward,tailLiveReward,historyMarkCount,hx]

-- Unfold List.tail inside implicit Decidable arguments during elaboration.
-- The resulting proof term still receives the ordinary kernel check.
set_option backward.isDefEq.respectTransparency false in
theorem whole_live_reward_succ (live P : S → Prop) (U : S → ℝ) (j : ℕ)
    (x : S) (xs : List S) :
    wholeLiveReward live P U (j+1) (x :: xs) =
      if P x then tailLiveReward live P U j (x :: xs)
      else tailLiveReward live P U (j+1) (x :: xs) := by
  by_cases hx : P x
  · unfold wholeLiveReward tailLiveReward
    simp only [historyMarkCount,hx,ite_true,List.tail_cons]
    by_cases h : (∀ z ∈ x :: xs, live z) ∧ historyMarkCount P xs = j
    · have h' : (∀ z ∈ x :: xs, live z) ∧ 1+historyMarkCount P xs = j+1 :=
        ⟨h.1,by omega⟩
      rw [ite_eq_left h',ite_eq_left h]
    · have h' : ¬((∀ z ∈ x :: xs, live z) ∧ 1+historyMarkCount P xs = j+1) := by
        intro hp
        exact h ⟨hp.1,by omega⟩
      rw [ite_eq_right h',ite_eq_right h]
  · simp [wholeLiveReward,tailLiveReward,historyMarkCount,hx]

theorem nnReward_congr_support {A : Type*} (p : PMF A) (f g : A → ℝ≥0∞)
    (h : ∀ a ∈ p.support, f a = g a) : nnReward p f = nnReward p g := by
  apply tsum_congr
  intro a
  by_cases ha : p a = 0
  · simp [ha]
  · rw [h a (by simpa only [PMF.mem_support_iff] using ha)]

variable [Fintype S]

theorem trajectory_support_cons (K : HybridCTMC.Kernel S) (n : ℕ) (x : S)
    (xs : List S) (hx : xs ∈ (K.trajectory n x).support) : ∃ ys, xs = x :: ys := by
  cases n with
  | zero =>
      have h : xs = [x] := by simpa only [Kernel.trajectory,PMF.mem_support_pure_iff] using hx
      exact ⟨[],h⟩
  | succ n =>
      obtain ⟨y,_,hy⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
      obtain ⟨ys,_,he⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
      exact ⟨ys,he.symm⟩

theorem trajectory_reward_cons (K : HybridCTMC.Kernel S) (live P : S → Prop)
    (U : S → ℝ) (n j : ℕ) (x y : S) :
    nnReward (K.trajectory n y) (fun xs => tailLiveReward live P U j (x :: xs)) =
      if live x then nnReward (K.trajectory n y) (wholeLiveReward live P U j) else 0 := by
  have he := nnReward_congr_support (K.trajectory n y)
    (fun xs => tailLiveReward live P U j (x :: xs))
    (fun xs => if live x then wholeLiveReward live P U j xs else 0) (by
      intro xs hs
      obtain ⟨ys,rfl⟩ := trajectory_support_cons K n y xs hs
      exact tail_live_reward_cons live P U j x y ys)
  rw [he]
  by_cases hx : live x <;> simp [hx,nnReward]

theorem trajectory_whole_zero (K : HybridCTMC.Kernel S) (live P : S → Prop)
    (U : S → ℝ) (n : ℕ) (x : S) :
    nnReward (K.trajectory n x) (wholeLiveReward live P U 0) =
      if P x then 0 else nnReward (K.trajectory n x) (tailLiveReward live P U 0) := by
  have he := nnReward_congr_support (K.trajectory n x)
    (wholeLiveReward live P U 0)
    (fun xs => if P x then 0 else tailLiveReward live P U 0 xs) (by
      intro xs hs
      obtain ⟨ys,rfl⟩ := trajectory_support_cons K n x xs hs
      exact whole_live_reward_zero live P U x ys)
  rw [he]
  by_cases hx : P x <;> simp [hx,nnReward]

theorem trajectory_whole_succ (K : HybridCTMC.Kernel S) (live P : S → Prop)
    (U : S → ℝ) (n j : ℕ) (x : S) :
    nnReward (K.trajectory n x) (wholeLiveReward live P U (j+1)) =
      if P x then nnReward (K.trajectory n x) (tailLiveReward live P U j)
      else nnReward (K.trajectory n x) (tailLiveReward live P U (j+1)) := by
  have he := nnReward_congr_support (K.trajectory n x)
    (wholeLiveReward live P U (j+1))
    (fun xs => if P x then tailLiveReward live P U j xs
      else tailLiveReward live P U (j+1) xs) (by
      intro xs hs
      obtain ⟨ys,rfl⟩ := trajectory_support_cons K n x xs hs
      exact whole_live_reward_succ live P U j x ys)
  rw [he]
  by_cases hx : P x <;> simp [hx]

theorem nnReward_kernel_ofReal (K : HybridCTMC.Kernel S) (f : S → ℝ)
    (hf : ∀ x, 0 ≤ f x) (x : S) :
    nnReward (K.pmf x) (fun y => ENNReal.ofReal (f y)) =
      ENNReal.ofReal (K.expect f x) := by
  rw [nnReward,tsum_fintype,Kernel.expect,
    ENNReal.ofReal_sum_of_nonneg (fun y _ => mul_nonneg (K.nonneg x y) (hf y))]
  apply Finset.sum_congr rfl
  intro y _
  rw [ENNReal.ofReal_mul (K.nonneg x y)]
  rfl

theorem nnReward_pointwise_le {A : Type*} (p : PMF A) (f g : A → ℝ≥0∞)
    (h : ∀ x, f x ≤ g x) : nnReward p f ≤ nnReward p g :=
  ENNReal.tsum_le_tsum (fun x => mul_le_mul_right (h x) (p x))

theorem trajectory_tail_live_succ (K : HybridCTMC.Kernel S) (live P : S → Prop)
    (U : S → ℝ) (n j : ℕ) (x : S) :
    nnReward (K.trajectory (n+1) x) (tailLiveReward live P U j) =
      if live x then nnReward (K.pmf x)
        (fun y => nnReward (K.trajectory n y) (wholeLiveReward live P U j)) else 0 := by
  rw [Kernel.trajectory,nnReward_bind]
  simp_rw [nnReward_map,trajectory_reward_cons]
  by_cases hx : live x <;> simp [hx,nnReward]

/-- Actual finite trajectory estimate. The assumptions are two explicit
one-step expectations under the given kernel, not probability estimates. -/
theorem trajectory_counted_live_bound (K : HybridCTMC.Kernel S)
    (live P : S → Prop) (U : S → ℝ) (a b : ℝ)
    (hU : ∀ x, 0 ≤ U x) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ x, live x →
      K.expect (fun y => if live y ∧ ¬P y then U y else 0) x ≤ a*U x)
    (hB : ∀ x, live x →
      K.expect (fun y => if live y ∧ P y then U y else 0) x ≤ b*U x)
    (n j : ℕ) (x : S) :
    nnReward (K.trajectory n x) (tailLiveReward live P U j) ≤
      ENNReal.ofReal (if live x then binomialWordCoefficient n j a b*U x else 0) := by
  induction n generalizing j x with
  | zero =>
      cases j <;> by_cases hx : live x <;>
        simp [Kernel.trajectory,nnReward_pure,tailLiveReward,historyMarkCount,
          historyTerminal,binomialWordCoefficient,hx]
  | succ n ih =>
      rw [trajectory_tail_live_succ]
      by_cases hx : live x
      · simp only [hx,ite_true]
        cases j with
        | zero =>
            let c := binomialWordCoefficient n 0 a b
            have hc : 0 ≤ c := word_coefficient_nonnegative n 0 a b ha hb
            let f : S → ℝ := fun y => if live y ∧ ¬P y then U y else 0
            have hf (y : S) : 0 ≤ f y := by
              dsimp [f]
              split_ifs
              · exact hU y
              · exact le_rfl
            have hp (y : S) :
                nnReward (K.trajectory n y) (wholeLiveReward live P U 0) ≤
                  ENNReal.ofReal (c*f y) := by
              rw [trajectory_whole_zero]
              by_cases hy : P y
              · simp [hy,f]
              · simpa [hy,f,c,mul_ite] using ih 0 y
            calc
              _ ≤ nnReward (K.pmf x) (fun y => ENNReal.ofReal (c*f y)) :=
                nnReward_pointwise_le _ _ _ hp
              _ = ENNReal.ofReal (c*K.expect f x) := by
                rw [nnReward_kernel_ofReal K _ (fun y => mul_nonneg hc (hf y)),K.expect_scale]
              _ ≤ ENNReal.ofReal (c*(a*U x)) :=
                ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hA x hx) hc)
              _ = _ := by rw [word_coefficient_zero]; congr 1; dsimp [c]; ring
        | succ j =>
            let c := binomialWordCoefficient n (j+1) a b
            let d := binomialWordCoefficient n j a b
            have hc : 0 ≤ c := word_coefficient_nonnegative n (j+1) a b ha hb
            have hd : 0 ≤ d := word_coefficient_nonnegative n j a b ha hb
            let f : S → ℝ := fun y => if live y ∧ ¬P y then U y else 0
            let g : S → ℝ := fun y => if live y ∧ P y then U y else 0
            have hf (y : S) : 0 ≤ f y := by
              dsimp [f]
              split_ifs
              · exact hU y
              · exact le_rfl
            have hg (y : S) : 0 ≤ g y := by
              dsimp [g]
              split_ifs
              · exact hU y
              · exact le_rfl
            have hp (y : S) :
                nnReward (K.trajectory n y) (wholeLiveReward live P U (j+1)) ≤
                  ENNReal.ofReal (c*f y+d*g y) := by
              rw [trajectory_whole_succ]
              by_cases hy : P y
              · simpa [hy,f,g,d,mul_ite] using ih j y
              · simpa [hy,f,g,c,mul_ite] using ih (j+1) y
            calc
              _ ≤ nnReward (K.pmf x) (fun y => ENNReal.ofReal (c*f y+d*g y)) :=
                nnReward_pointwise_le _ _ _ hp
              _ = ENNReal.ofReal (c*K.expect f x+d*K.expect g x) := by
                rw [nnReward_kernel_ofReal K _
                  (fun y => add_nonneg (mul_nonneg hc (hf y)) (mul_nonneg hd (hg y))),
                  K.expect_add,K.expect_scale,K.expect_scale]
              _ ≤ ENNReal.ofReal (c*(a*U x)+d*(b*U x)) :=
                ENNReal.ofReal_le_ofReal (add_le_add
                  (mul_le_mul_of_nonneg_left (hA x hx) hc)
                  (mul_le_mul_of_nonneg_left (hB x hx) hd))
              _ = _ := by rw [word_coefficient_pascal]; congr 1; dsimp [c,d]; ring
      · simp [hx]

end
end P161Formal

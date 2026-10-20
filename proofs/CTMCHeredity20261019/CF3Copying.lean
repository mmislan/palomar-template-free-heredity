module

public import proofs.FunctionalCapacity.SiteCF3
public import proofs.TemplateFreeHeredity.FairBinomialTail

@[expose] public section

/-!
# Actual CF3 complementary daughter copying

These are local copying statements for the literal CF3 `ps`, `td`, `d1`, and
`d2` operations. All fuel configurations and all external ledgers are arbitrary.
The parent-ready premise is imposed at the actual division prestate; readiness
at an earlier stopping time alone does not supply it. No timed path bridge or
mission-level probability is assumed here.
-/

namespace CTMCHeredity20261019

open MeasureTheory FunctionalCapacity
open scoped BigOperators Classical

noncomputable section

/-- The existing scalar binomial expectation is the actual fair allocation
measure on indicator observables. -/
theorem binE_indicator_eq_fairAllocationMeasure (n : ℕ) (A : ℕ → Prop) :
    binE (fun k => if A k then (1 : ℝ) else 0) n =
      (CompositionalMemory.fairAllocationMeasure n).real {k | A k} := by
  classical
  have hm : MeasurableSet {k : ℕ | A k} := MeasurableSet.of_discrete
  have hI := CompositionalMemory.fairAllocationMeasure_integral n
    (fun k => if A k then (1 : ℝ) else 0)
  have hM :
      (∫ k, (if A k then (1 : ℝ) else 0)
        ∂CompositionalMemory.fairAllocationMeasure n) =
        (CompositionalMemory.fairAllocationMeasure n).real {k | A k} := by
    simpa [Set.indicator] using
      (integral_indicator_one
        (μ := CompositionalMemory.fairAllocationMeasure n) hm)
  rw [hI] at hM
  simpa only [binE, HeritableCompositions.fairBinomialWeight] using hM

/-- The exact deviation needed by a floor16 failure at any parent count at
least512 has a Chernoff exponent at least225. -/
theorem ready512_copying_exponent (n : ℕ) (hn : 512 ≤ n) :
    225 ≤ 2 * ((n : ℝ) / 2 - 16) ^ 2 / n := by
  have hnR : (512 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  apply (le_div_iff₀ hn0).2
  have hp : 0 ≤ ((n : ℝ) - 512) * ((n : ℝ) - 2) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- Both sisters are tested together, using a single complementary draw. -/
theorem binE_complementary_floor16_failure_le (n : ℕ) (hn : 512 ≤ n) :
    binE (fun k => if k < 16 ∨ n - k < 16 then (1 : ℝ) else 0) n ≤
      2 * Real.exp (-225) := by
  classical
  let μ := CompositionalMemory.fairAllocationMeasure n
  let δ : ℝ := (n : ℝ) / 2 - 16
  have hnR : (512 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < n := by omega
  have hδ : 0 ≤ δ := by dsimp [δ]; linarith
  have hsub : {k : ℕ | k < 16 ∨ n - k < 16} ⊆
      {k : ℕ | δ ≤ |(k : ℝ) - (n : ℝ) / 2|} := by
    intro k hk
    change δ ≤ |(k : ℝ) - (n : ℝ) / 2|
    rcases hk with hk | hk
    · have hkR : (k : ℝ) < 16 := by exact_mod_cast hk
      have ha := neg_le_abs ((k : ℝ) - (n : ℝ) / 2)
      dsimp [δ]
      linarith
    · have ha := le_abs_self ((k : ℝ) - (n : ℝ) / 2)
      by_cases hkn : k ≤ n
      · have hkR : ((n - k : ℕ) : ℝ) < 16 := by exact_mod_cast hk
        rw [Nat.cast_sub hkn] at hkR
        dsimp [δ]
        linarith
      · have hnk : (n : ℝ) < k := by exact_mod_cast (by omega : n < k)
        dsimp [δ]
        linarith
  have hmono := measureReal_mono (μ := μ) hsub (by finiteness)
  have htail := TemplateFreeHeredity.fairAllocation_two_sided_tail n hn0 δ hδ
  have hexp : -2 * δ ^ 2 / n ≤ -225 := by
    have he := ready512_copying_exponent n hn
    dsimp [δ]
    calc
      -2 * ((n : ℝ) / 2 - 16) ^ 2 / n =
          -(2 * ((n : ℝ) / 2 - 16) ^ 2 / n) := by ring
      _ ≤ -225 := neg_le_neg he
  -- A named indicator fixes its decision procedure. The source statement has
  -- the computable natural-order decider, whereas the measure bridge's
  -- abstract predicate has the classical decider; compare their values.
  let A : ℕ → Prop := fun k => k < 16 ∨ n - k < 16
  let g : ℕ → ℝ := fun k => @ite ℝ (A k) (Classical.propDecidable (A k)) 1 0
  have hg : (fun k => if k < 16 ∨ n - k < 16 then (1 : ℝ) else 0) = g := by
    funext k
    dsimp only [g, A]
    by_cases hk : k < 16 ∨ n - k < 16
    · simp only [ite_eq_left hk]
    · simp only [ite_eq_right hk]
  calc
    _ = binE g n := congrArg (fun f => binE f n) hg
    _ = μ.real {k | A k} := binE_indicator_eq_fairAllocationMeasure n A
    _ ≤ μ.real {k | δ ≤ |(k : ℝ) - (n : ℝ) / 2|} := hmono
    _ ≤ 2 * Real.exp (-2 * δ ^ 2 / n) := htail
    _ ≤ 2 * Real.exp (-225) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by norm_num)

/-- The local failure event for one species under the literal split mark. -/
def coordinateCopyingFailure {p : Par} (s : Site p.c p.N)
    (o : Split p.c p.N) (j : Fin p.c) : Prop :=
  (o.1 j : ℕ) < 16 ∨ (s.a j : ℕ) - (o.1 j : ℕ) < 16

/-- Sum of the actual CF3 split weights of a one-coordinate copying failure. -/
theorem cf3_coordinate_copying_failure_le {p : Par} (s : Site p.c p.N)
    (j : Fin p.c) (hs : 512 ≤ (s.a j : ℕ)) :
    (∑ o, (cf3 p).ps s o *
      (if coordinateCopyingFailure s o j then (1 : ℝ) else 0)) ≤
      2 * Real.exp (-225) := by
  classical
  let A : ℕ → Prop := fun k => k < 16 ∨ (s.a j : ℕ) - k < 16
  let g : ℕ → ℝ := fun k => @ite ℝ (A k) (Classical.propDecidable (A k)) 1 0
  have hm := cf3_ps_marg s j (fun k _ => g k)
  have hleft : (∑ o, (cf3 p).ps s o *
      (if coordinateCopyingFailure s o j then (1 : ℝ) else 0)) =
      ∑ o, (cf3 p).ps s o * g (o.1 j) := by
    apply Finset.sum_congr rfl
    intro o _
    apply congrArg (fun a => (cf3 p).ps s o * a)
    by_cases ho : coordinateCopyingFailure s o j
    · have ha : A (o.1 j) := ho
      simp only [g, ite_eq_left ho, ite_eq_left ha]
    · have ha : ¬ A (o.1 j) := ho
      simp only [g, ite_eq_right ho, ite_eq_right ha]
  have hright : g =
      (fun k => if k < 16 ∨ (s.a j : ℕ) - k < 16 then (1 : ℝ) else 0) := by
    funext k
    dsimp only [g, A]
    by_cases hk : k < 16 ∨ (s.a j : ℕ) - k < 16
    · simp only [ite_eq_left hk]
    · simp only [ite_eq_right hk]
  calc
    _ = ∑ o, (cf3 p).ps s o * g (o.1 j) := hleft
    _ = (binE g (s.a j : ℕ) + binE g (s.a j : ℕ)) / 2 := hm
    _ = binE g (s.a j : ℕ) := by ring
    _ = binE
        (fun k => if k < 16 ∨ (s.a j : ℕ) - k < 16 then (1 : ℝ) else 0)
        (s.a j : ℕ) := congrArg (fun f => binE f (s.a j : ℕ)) hright
    _ ≤ 2 * Real.exp (-225) := binE_complementary_floor16_failure_le _ hs

/-- Union bound for the actual joint CF3 split law. The sisters are complementary;
neither their independence nor independence of failures between species is used. -/
theorem cf3_both_daughters_failure_le {p : Par} (s : Site p.c p.N)
    (hs : ∀ j, 512 ≤ (s.a j : ℕ)) :
    (∑ o, (cf3 p).ps s o *
      (if ∃ j, coordinateCopyingFailure s o j then (1 : ℝ) else 0)) ≤
      (p.c : ℝ) * (2 * Real.exp (-225)) := by
  classical
  have hpoint (o : Split p.c p.N) :
      (if ∃ j, coordinateCopyingFailure s o j then (1 : ℝ) else 0) ≤
        ∑ j, if coordinateCopyingFailure s o j then (1 : ℝ) else 0 := by
    by_cases h : ∃ j, coordinateCopyingFailure s o j
    · obtain ⟨j, hj⟩ := h
      rw [ite_eq_left ⟨j, hj⟩]
      have hsingle := Finset.single_le_sum
        (f := fun j => if coordinateCopyingFailure s o j then (1 : ℝ) else 0)
        (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ j)
      simpa only [ite_eq_left hj] using hsingle
    · rw [ite_eq_right h]
      exact Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num
  calc
    _ ≤ ∑ o, (cf3 p).ps s o *
        ∑ j, if coordinateCopyingFailure s o j then (1 : ℝ) else 0 :=
      Finset.sum_le_sum fun o _ =>
        mul_le_mul_of_nonneg_left (hpoint o) (cf3_ps_nonneg s o)
    _ = ∑ j, ∑ o, (cf3 p).ps s o *
        (if coordinateCopyingFailure s o j then (1 : ℝ) else 0) := by
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    _ ≤ ∑ _j : Fin p.c, 2 * Real.exp (-225) :=
      Finset.sum_le_sum fun j _ => cf3_coordinate_copying_failure_le s j (hs j)
    _ = (p.c : ℝ) * (2 * Real.exp (-225)) := by simp

/-- The actual division channel changes fuel and external counters, but preserves
all parent counts before applying the complementary split. -/
theorem cf3_td_count {p : Par} (s : Site p.c p.N)
    (k : Option (Fin p.c)) (j : Fin p.c) :
    ((cf3 p).td s k).a j = s.a j := by
  cases k <;> rfl

/-- Source-facing copying bound for either actual CF3 division channel with three
species. It refers to both actual daughters of one parent and arbitrary ledgers. -/
theorem cf3_actual_division_copying_three {p : Par} (hc : p.c = 3)
    (s : Site p.c p.N) (k : Option (Fin p.c))
    (hs : ∀ j, 512 ≤ (s.a j : ℕ)) :
    (∑ o, (cf3 p).ps ((cf3 p).td s k) o *
      (if ∃ j,
        (((cf3 p).d1 ((cf3 p).td s k) o).a j : ℕ) < 16 ∨
        (((cf3 p).d2 ((cf3 p).td s k) o).a j : ℕ) < 16
      then (1 : ℝ) else 0)) ≤ 6 * Real.exp (-225) := by
  have h := cf3_both_daughters_failure_le ((cf3 p).td s k)
    (fun j => by simpa only [cf3_td_count] using hs j)
  have hind (o : Split p.c p.N) :
      (if ∃ j,
        (((cf3 p).d1 ((cf3 p).td s k) o).a j : ℕ) < 16 ∨
        (((cf3 p).d2 ((cf3 p).td s k) o).a j : ℕ) < 16
      then (1 : ℝ) else 0) =
      (if ∃ j, coordinateCopyingFailure ((cf3 p).td s k) o j
      then (1 : ℝ) else 0) := by
    have hevent : (∃ j,
        (((cf3 p).d1 ((cf3 p).td s k) o).a j : ℕ) < 16 ∨
        (((cf3 p).d2 ((cf3 p).td s k) o).a j : ℕ) < 16) ↔
        ∃ j, coordinateCopyingFailure ((cf3 p).td s k) o j := Iff.rfl
    by_cases ho : ∃ j, coordinateCopyingFailure ((cf3 p).td s k) o j
    · have ha := hevent.mpr ho
      simp only [ite_eq_left ha, ite_eq_left ho]
    · have ha : ¬ (∃ j,
          (((cf3 p).d1 ((cf3 p).td s k) o).a j : ℕ) < 16 ∨
          (((cf3 p).d2 ((cf3 p).td s k) o).a j : ℕ) < 16) :=
        fun ha => ho (hevent.mp ha)
      simp only [ite_eq_right ha, ite_eq_right ho]
  calc
    _ = ∑ o, (cf3 p).ps ((cf3 p).td s k) o *
        (if ∃ j, coordinateCopyingFailure ((cf3 p).td s k) o j
        then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro o _
      exact congrArg (fun a => (cf3 p).ps ((cf3 p).td s k) o * a) (hind o)
    _ ≤ (p.c : ℝ) * (2 * Real.exp (-225)) := h
    _ = 6 * Real.exp (-225) := by rw [hc]; norm_num; ring

/-- The canonical beta4m seed-free source, with precisely its physical parameters. -/
def canonicalSeedFreeCF3 : Par := ⟨4, 3, 2048, 800, 4000000, 0⟩

set_option maxHeartbeats 2000000 in
/-- A concrete canonical-source instance; no rate, fuel, or ledger assumption
is hidden in the local partition statement. -/
theorem canonical_seed_free_division_copying (s : Site 3 2048)
    (k : Option (Fin 3)) (hs : ∀ j, 512 ≤ (s.a j : ℕ)) :
    (∑ o, (cf3 canonicalSeedFreeCF3).ps ((cf3 canonicalSeedFreeCF3).td s k) o *
      (if ∃ j,
        (((cf3 canonicalSeedFreeCF3).d1 ((cf3 canonicalSeedFreeCF3).td s k) o).a j : ℕ) < 16 ∨
        (((cf3 canonicalSeedFreeCF3).d2 ((cf3 canonicalSeedFreeCF3).td s k) o).a j : ℕ) < 16
      then (1 : ℝ) else 0)) ≤ 6 * Real.exp (-225) :=
  cf3_actual_division_copying_three (p := canonicalSeedFreeCF3) rfl s k hs

end
end CTMCHeredity20261019

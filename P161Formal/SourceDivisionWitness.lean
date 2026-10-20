module

public import P161Formal.BranchingSourceGuards
public import proofs.FunctionalCapacity.SiteCF3c

/-! The spatial initiating-division witness for at least five divisions per
site after withdrawal. Victim ledger semantics are those of the actual source. -/

@[expose] public section
namespace P161Formal
open FunctionalCapacity CTMCHeredity20261019
open scoped BigOperators Classical
noncomputable section

def sourceDivisionPotential (x : BranchingSource) : ℝ :=
  ∑ i : SiteId, (1/6 : ℝ)^((x i).nd)

theorem source_division_potential_bounds (x : BranchingSource) :
    0 ≤ sourceDivisionPotential x ∧ sourceDivisionPotential x ≤ 4 := by
  constructor
  · exact Finset.sum_nonneg (fun i _ => pow_nonneg (by norm_num) ((x i).nd))
  · calc
      _ ≤ ∑ _i : SiteId, (1 : ℝ) := Finset.sum_le_sum
        (fun _i _ => pow_le_one₀ (by norm_num) (by norm_num))
      _ = 4 := by norm_num

theorem source_generator_finset_sum {I : Type} (seed : ℝ) (hs : 0 ≤ seed)
    (s : Finset I) (F : I → BranchingSource → ℝ) (x : BranchingSource) :
    cf3Gen (literalSourcePar seed) (fun y => ∑ i ∈ s, F i y) x =
      ∑ i ∈ s, cf3Gen (literalSourcePar seed) (F i) x := by
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact generatorKilled_zero (cf3_isGen (literal_source_valid seed hs)) x
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [(cf3_isGen (literal_source_valid seed hs)).add,ih]

theorem source_division_potential_drift (seed : ℝ) (hs : 0 ≤ seed) (x : BranchingSource) :
    cf3Gen (literalSourcePar seed) sourceDivisionPotential x ≤
      -(5/6 : ℝ)*sourceDivisionPotential x := by
  have hd (n : ℕ) : (1/6 : ℝ)^(n+1) ≤ (1/6 : ℝ)^n :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)
  change cf3Gen (literalSourcePar seed)
    (fun y => ∑ i : SiteId, (1/6 : ℝ)^((y i).nd)) x ≤ _
  rw [source_generator_finset_sum seed hs]
  calc
    _ ≤ ∑ i : SiteId, (-((1/6 : ℝ)^((x i).nd)-(1/6 : ℝ)^((x i).nd+1))) :=
      Finset.sum_le_sum (fun i _ => cf3Gen_div (literal_source_valid seed hs) i
        (fun n => (1/6 : ℝ)^n) hd x)
    _ = _ := by
      simp only [pow_succ,Finset.sum_neg_distrib,Finset.sum_sub_distrib,
        ←Finset.sum_mul,sourceDivisionPotential]
      ring

theorem source_division_reset_q (seed : ℝ) (x : BranchingSource) :
    sourceDivisionPotential (sourceResetQ (p := literalSourcePar seed) x) =
      sourceDivisionPotential x := rfl

theorem source_division_reset_all (seed : ℝ) (x : BranchingSource) :
    sourceDivisionPotential (sourceResetAll (p := literalSourcePar seed) x) = 4 := by
  simp [sourceDivisionPotential,sourceResetAll]

theorem source_division_terminal_lower (x : BranchingSource) :
    1-branchingAllPotential x-1296*sourceDivisionPotential x ≤ sourceFinalD 5 x := by
  have hPhi := branching_all_nonnegative x
  have hD := (source_division_potential_bounds x).1
  unfold sourceFinalD
  split_ifs with h
  · nlinarith
  · push Not at h
    obtain ⟨i,hi⟩ := h
    have hp : (1/6 : ℝ)^4 ≤ (1/6 : ℝ)^((x i).nd) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hm : (1/6 : ℝ)^((x i).nd) ≤ sourceDivisionPotential x :=
      Finset.single_le_sum (f := fun k : SiteId => (1/6 : ℝ)^((x k).nd))
        (fun k _ => pow_nonneg (by norm_num) ((x k).nd)) (Finset.mem_univ i)
    norm_num at hp
    linarith

end
end P161Formal

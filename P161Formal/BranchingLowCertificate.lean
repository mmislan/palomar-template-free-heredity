module

public import P161Formal.BranchingLowPilot
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! Exact104-vertex low-count certificate and its affine rectangle soundness.
Compilation is gated by the separate four-case pilot and bounded plan. -/

@[expose] public section
namespace P161Formal

theorem branching_low_vertices : (List.range 13).all (fun a =>
    [false,true].all (fun fuel => ([0,2] : List ℚ).all (fun U =>
      ([0,1843200] : List ℚ).all (fun v => decide
        (branchingSiteOperatorQ a fuel U v 6+branchingWitnessQ a fuel/2 ≤
          (13/10000000 : ℚ)))))) = true := by
  decide +kernel

theorem branching_low_vertex_bound (a : ℕ) (ha : a ≤ 12) (fuel : Bool)
    (U v : ℚ) (hU : U ∈ ([0,2] : List ℚ)) (hv : v ∈ ([0,1843200] : List ℚ)) :
    branchingSiteOperatorQ a fuel U v 6+branchingWitnessQ a fuel/2 ≤ 13/10000000 := by
  have h := List.all_eq_true.mp branching_low_vertices a (by
    simp only [List.mem_range]
    omega)
  have hf : fuel ∈ [false,true] := by cases fuel <;> simp
  have h := List.all_eq_true.mp h fuel hf
  have h := List.all_eq_true.mp h U hU
  exact of_decide_eq_true (List.all_eq_true.mp h v hv)

theorem rational_affine_interval_le (m n lo hi x b : ℚ)
    (hlo : lo ≤ x) (hhi : x ≤ hi)
    (h0 : m*lo+n ≤ b) (h1 : m*hi+n ≤ b) : m*x+n ≤ b := by
  rcases le_total 0 m with hm | hm
  · have h := mul_nonneg hm (sub_nonneg.mpr hhi)
    nlinarith
  · have h := mul_nonneg (neg_nonneg.mpr hm) (sub_nonneg.mpr hlo)
    nlinarith

theorem branching_operator_affine_foreign (a : ℕ) (fuel : Bool) (U v seed : ℚ) :
    branchingSiteOperatorQ a fuel U v seed =
      U*((branchingSiteOperatorQ a fuel 2 v seed-
        branchingSiteOperatorQ a fuel 0 v seed)/2)+
          branchingSiteOperatorQ a fuel 0 v seed := by
  cases fuel <;> dsimp [branchingSiteOperatorQ] <;> ring

theorem branching_operator_affine_consumption (a : ℕ) (fuel : Bool) (U v seed : ℚ) :
    branchingSiteOperatorQ a fuel U v seed =
      v*((branchingSiteOperatorQ a fuel U 1843200 seed-
        branchingSiteOperatorQ a fuel U 0 seed)/1843200)+
          branchingSiteOperatorQ a fuel U 0 seed := by
  cases fuel <;> dsimp [branchingSiteOperatorQ] <;> ring

theorem branching_low_seeded_drift (a : ℕ) (ha : a ≤ 12) (fuel : Bool)
    (U v : ℚ) (hU0 : 0 ≤ U) (hU1 : U ≤ 2) (hv0 : 0 ≤ v) (hv1 : v ≤ 1843200) :
    branchingSiteOperatorQ a fuel U v 6 ≤ -branchingWitnessQ a fuel/2+13/10000000 := by
  have hfixed (w : ℚ) (hw : w ∈ ([0,1843200] : List ℚ)) :
      branchingSiteOperatorQ a fuel U w 6 ≤ -branchingWitnessQ a fuel/2+13/10000000 := by
    have h0 := branching_low_vertex_bound a ha fuel 0 w (by simp) hw
    have h2 := branching_low_vertex_bound a ha fuel 2 w (by simp) hw
    rw [branching_operator_affine_foreign a fuel U w 6]
    have h := rational_affine_interval_le
      ((branchingSiteOperatorQ a fuel 2 w 6-branchingSiteOperatorQ a fuel 0 w 6)/2)
      (branchingSiteOperatorQ a fuel 0 w 6) 0 2 U
      (-branchingWitnessQ a fuel/2+13/10000000) hU0 hU1 (by nlinarith) (by nlinarith)
    nlinarith
  have h0 := hfixed 0 (by simp)
  have h1 := hfixed 1843200 (by simp)
  rw [branching_operator_affine_consumption a fuel U v 6]
  have h := rational_affine_interval_le
    ((branchingSiteOperatorQ a fuel U 1843200 6-branchingSiteOperatorQ a fuel U 0 6)/1843200)
    (branchingSiteOperatorQ a fuel U 0 6) 0 1843200 v
    (-branchingWitnessQ a fuel/2+13/10000000) hv0 hv1 (by nlinarith) (by nlinarith)
  nlinarith

end P161Formal

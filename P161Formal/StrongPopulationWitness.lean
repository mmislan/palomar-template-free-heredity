module

public import P161Formal.StrongRecoveryCertificate
public import P161Formal.Contract
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Deterministic population bounds for the checked recovery witness.
The barrier applies at the actual current population, independently of any
future floor-success event. No stochastic expectation premise is introduced. -/

@[expose] public section
namespace P161Formal
open scoped BigOperators

theorem strong_underfloor_zero (a : ℕ) (fuel : Bool) (ha : a < 16) :
    strongRecoveryWitnessQ a fuel = 0 := by
  have hchecked : (List.range 16).all (fun a => decide
      (strongRecoveryWitnessQ a false = 0 ∧ strongRecoveryWitnessQ a true = 0)) = true := by
    decide +kernel
  have h := List.all_eq_true.mp hchecked a (by simpa only [List.mem_range] using ha)
  have hh : strongRecoveryWitnessQ a false = 0 ∧ strongRecoveryWitnessQ a true = 0 :=
    of_decide_eq_true h
  cases fuel
  · exact hh.1
  · exact hh.2

theorem strong_coordinate_nonnegative (a : ℕ) (fuel : Bool) (hb : a ≤ 2048) :
    0 ≤ strongRecoveryWitnessQ a fuel := by
  by_cases h : a < 16
  · rw [strong_underfloor_zero a fuel h]
  · have hs := strong_witness_shape a (by omega) hb
    cases fuel
    · exact le_trans (le_of_lt hs.1) hs.2.1
    · exact le_of_lt hs.1

theorem strong_coordinate_scaled_max (a : ℕ) (fuel : Bool) (hb : a ≤ 2048) :
    12 * strongRecoveryWitnessQ a fuel ≤ (338971453059/125000 : ℚ) := by
  by_cases h : a < 16
  · rw [strong_underfloor_zero a fuel h]
    norm_num
  · have hs := strong_witness_shape a (by omega) hb
    cases fuel
    · exact hs.2.2.1
    · nlinarith [hs.2.1,hs.2.2.1]

def strongPopulationPotentialQ (x : Population) : ℚ :=
  ∑ i : SiteId, ∑ j : SpeciesId, strongRecoveryWitnessQ (x.count i j).val (x.fuel i)

theorem strong_population_nonnegative (x : Population) : 0 ≤ strongPopulationPotentialQ x := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact strong_coordinate_nonnegative _ _ (by have h := (x.count i j).isLt; omega)

theorem strong_population_max (x : Population) :
    strongPopulationPotentialQ x ≤ (338971453059/125000 : ℚ) := by
  have hcell (i : SiteId) (j : SpeciesId) :
      strongRecoveryWitnessQ (x.count i j).val (x.fuel i) ≤ (338971453059/125000 : ℚ)/12 := by
    have h := strong_coordinate_scaled_max (x.count i j).val (x.fuel i)
      (by have h := (x.count i j).isLt; omega)
    linarith
  calc
    strongPopulationPotentialQ x ≤
        ∑ _i : SiteId, ∑ _j : SpeciesId, (338971453059/125000 : ℚ)/12 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hcell i j))
    _ = 338971453059/125000 := by norm_num

theorem strong_nonready_barrier (x : Population)
    (hfloor : floorFor x (fun _ => True)) (hnot : ¬ready512 x) :
    1 ≤ strongPopulationPotentialQ x := by
  have hex : ∃ i j, (x.count i j).val < 512 := by
    by_contra h
    apply hnot
    intro i j
    by_contra hlow
    exact h ⟨i,j,by omega⟩
  obtain ⟨i,j,hsmall⟩ := hex
  have hs := strong_witness_shape (x.count i j).val (hfloor i j True.intro)
    (by have h := (x.count i j).isLt; omega)
  have ht : 1 ≤ strongRecoveryWitnessQ (x.count i j).val true := by
    simpa only [ite_eq_left hsmall] using hs.2.2.2
  have hc : 1 ≤ strongRecoveryWitnessQ (x.count i j).val (x.fuel i) := by
    cases hR : x.fuel i
    · exact le_trans ht hs.2.1
    · exact ht
  have hrow := Finset.single_le_sum
    (fun (k : SpeciesId) (_ : k ∈ Finset.univ) => strong_coordinate_nonnegative
      (x.count i k).val (x.fuel i) (by have h := (x.count i k).isLt; omega))
    (Finset.mem_univ j)
  have htotal := Finset.single_le_sum
    (fun (k : SiteId) (_ : k ∈ Finset.univ) => Finset.sum_nonneg
      (fun (l : SpeciesId) (_ : l ∈ Finset.univ) => strong_coordinate_nonnegative
        (x.count k l).val (x.fuel k) (by have h := (x.count k l).isLt; omega)))
    (Finset.mem_univ i)
  exact le_trans hc (le_trans hrow htotal)

theorem strong_ready_upper_bound (x : Population) (hready : ready512 x) :
    strongPopulationPotentialQ x ≤ 12 := by
  have hcell (i : SiteId) (j : SpeciesId) :
      strongRecoveryWitnessQ (x.count i j).val (x.fuel i) ≤ 1 := by
    have ha := hready i j
    have hs := strong_witness_shape (x.count i j).val (by omega)
      (by have h := (x.count i j).isLt; omega)
    have hfalse : strongRecoveryWitnessQ (x.count i j).val false ≤ 1 := by
      simpa only [strongRecoveryWitnessQ,recoveryAQ,
        ite_eq_right (show ¬(x.count i j).val < 512 by omega),Bool.false_eq_true,ite_false,sub_zero]
        using recovery_tail_at_most_one (x.count i j).val ha
    cases hR : x.fuel i
    · exact hfalse
    · exact le_trans hs.2.1 hfalse
  calc
    strongPopulationPotentialQ x ≤ ∑ _i : SiteId, ∑ _j : SpeciesId, (1 : ℚ) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hcell i j))
    _ = 12 := by norm_num

end P161Formal

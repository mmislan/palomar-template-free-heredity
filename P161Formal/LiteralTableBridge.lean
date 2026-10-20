module

public import P161Formal.TailEnclosureCertificate
public import P161Formal.ResetChecker
public import P161Formal.ChemicalDriftBounds

/-! Real table comparisons used by the source reset gain. The low-table
membership is proved from the authenticated full/low list identity, and the
integer predecessor is exactly the nonnegative rounded-down table value. -/

@[expose] public section
namespace P161Formal
noncomputable section

abbrev profileEntry (a : ℕ) (fuel : Bool) : ℝ := profileEntryQ a fuel

def resetTableLower (a : ℕ) (fuel : Bool) : ℝ :=
  let p := fullProfilePairs[a]?.getD (0,0)
  (((if fuel then p.2 else p.1)-1 : ℕ) : ℝ)/10^18

theorem natural_grid_predecessor (n : ℕ) :
    ((n-1 : ℕ) : ℝ)/10^18 = max 0 ((n : ℝ)/10^18-1/10^18) := by
  cases n with
  | zero => norm_num
  | succ n =>
      simp only [Nat.succ_sub_one,Nat.cast_succ]
      have h : ((n : ℝ)+1)/10^18-1/10^18 = (n : ℝ)/10^18 := by ring
      rw [h,max_eq_right (by positivity)]

theorem reset_table_lower_eq (a : ℕ) (fuel : Bool) :
    resetTableLower a fuel = max 0 (profileEntry a fuel-1/10^18) := by
  have hden : ((10^18 : ℚ) : ℝ) = (10 : ℝ)^18 := by norm_num
  cases fuel <;>
    simpa only [resetTableLower,profileEntry,profileEntryQ,Bool.false_eq_true,
      ite_false,ite_true,Rat.cast_div,Rat.cast_natCast,hden] using
        natural_grid_predecessor _

theorem full_low_pair_member (a : ℕ) (ha : 16 ≤ a) (hb : a < 512) :
    fullProfilePairs[a]?.getD (0,0) ∈ lowProfilePairs := by
  have hi : a < fullProfilePairs.length := by rw [full_profile_length]; omega
  have hget : fullProfilePairs[a]? = some (fullProfilePairs[a]?.getD (0,0)) := by
    simp only [List.getElem?_eq_getElem hi,Option.getD_some]
  have hindex : ((fullProfilePairs.drop 16).take 496)[a-16]? = fullProfilePairs[a]? := by
    rw [List.getElem?_take_of_lt (show a-16 < 496 by omega),List.getElem?_drop]
    congr 1
    omega
  have ht := hindex.trans hget
  rw [full_profile_low_agrees] at ht
  exact List.mem_of_getElem? ht

theorem strong_low_table_comparison (a : ℕ) (fuel : Bool)
    (ha : 16 ≤ a) (hb : a < 512) :
    (9993/10000 : ℝ)*max 0 (profileEntry a fuel-1/10^18) ≤
      strongRecoveryWitness a fuel ∧ strongRecoveryWitness a fuel ≤ profileEntry a false := by
  let p := fullProfilePairs[a]?.getD (0,0)
  have hp := full_low_pair_member a ha hb
  let A : ℝ := (p.1 : ℝ)/10^18
  let D : ℝ := ((p.1 : ℝ)-(p.2 : ℝ))/10^18
  obtain ⟨hrawA,horder,hrawD⟩ := low_profile_row p hp
  have hAr : (0 : ℝ) < p.1 := by exact_mod_cast hrawA
  have horderR : (p.2 : ℝ) ≤ p.1 := by exact_mod_cast horder
  have hsmallR : (1251 : ℝ)*((p.1-p.2 : ℕ) : ℝ) ≤ p.1 := by exact_mod_cast hrawD
  rw [Nat.cast_sub horder] at hsmallR
  have hpos : 0 < A := by dsimp [A]; positivity
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hD1 : D ≤ A/1251 := by dsimp [A,D]; nlinarith
  have hm : max 0 (A-D-1/10^18) ≤ A-D := max_le (by nlinarith) (by norm_num)
  have hcomp : (9993/10000 : ℝ)*max 0 (A-D-1/10^18) ≤ A-(15/8)*D := by nlinarith
  have hP0 : profileEntry a false = A := by
    norm_num [profileEntry,profileEntryQ,A,p]
  have hP1 : profileEntry a true = A-D := by
    norm_num [profileEntry,profileEntryQ,A,D,p]
    ring
  have hH0 : strongRecoveryWitness a false = A := by
    norm_num [strongRecoveryWitness,strongRecoveryWitnessQ,recoveryAQ,hb,profileEntryQ,A,p]
  have hH1 : strongRecoveryWitness a true = A-(15/8)*D := by
    norm_num [strongRecoveryWitness,strongRecoveryWitnessQ,recoveryAQ,recoveryGapQ,hb,
      profileEntryQ,A,D,p]
    ring
  cases fuel
  · rw [hP0,hH0]
    have hm : max 0 (A-1/10^18) ≤ A := max_le hpos.le (by norm_num)
    exact ⟨by nlinarith,le_rfl⟩
  · rw [hP1,hP0,hH1]
    exact ⟨hcomp,by nlinarith⟩

theorem strong_table_comparison (a : ℕ) (fuel : Bool) (ha : 16 ≤ a) (hb : a ≤ 2048) :
    (9993/10000 : ℝ)*resetTableLower a fuel ≤ strongRecoveryWitness a fuel ∧
      strongRecoveryWitness a fuel ≤ profileEntry a false := by
  rw [reset_table_lower_eq]
  by_cases hlo : a < 512
  · exact strong_low_table_comparison a fuel ha hlo
  · have h := strong_high_table_comparison a fuel (by omega) hb
    have hden : ((10^18 : ℚ) : ℝ) = (10 : ℝ)^18 := by norm_num
    constructor
    · have hr := (Rat.cast_le (K := ℝ)).mpr h.1
      simpa only [Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,Rat.cast_max,
        Rat.cast_zero,Rat.cast_sub,Rat.cast_one,hden,strongRecoveryWitness,profileEntry]
        using hr
    · exact (Rat.cast_le (K := ℝ)).mpr h.2

end
end P161Formal

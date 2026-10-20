module

public import P161Formal.SourceResetRateBounds
public import P161Formal.PairedBinomialMoment

/-! The actual joint source split, averaged with its original binomial/fuel
law, yields the paired table moment for the two complementary daughters. -/

@[expose] public section
namespace P161Formal
open scoped BigOperators
noncomputable section

theorem profile_entry_nonnegative (a : ℕ) (fuel : Bool) : 0 ≤ profileEntry a fuel := by
  apply Rat.cast_nonneg.mpr
  unfold profileEntryQ
  positivity

def pairedDaughterTable (a k : ℕ) : ℝ :=
  if 16 ≤ k ∧ 16 ≤ a-k then profileEntry k false+profileEntry (a-k) false else 0

theorem paired_daughter_table_nonnegative (a k : ℕ) : 0 ≤ pairedDaughterTable a k := by
  unfold pairedDaughterTable
  split_ifs
  · exact add_nonneg (profile_entry_nonnegative k false) (profile_entry_nonnegative (a-k) false)
  · exact le_rfl

theorem binE_paired_daughters (a : ℕ) :
    FunctionalCapacity.binE (pairedDaughterTable a) a = 2*pairedTableMoment a := by
  have hsplit : FunctionalCapacity.binE (pairedDaughterTable a) a =
      pairedBinomialMoment (fun k => profileEntry k false) a +
        ∑ k ∈ Finset.range (a+1), (a.choose k : ℝ)/2^a*
          (if 16 ≤ k ∧ 16 ≤ a-k then profileEntry (a-k) false else 0) := by
    unfold FunctionalCapacity.binE pairedBinomialMoment
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    unfold pairedDaughterTable
    split_ifs <;> ring
  rw [hsplit,paired_binomial_complement (fun k => profileEntry k false) a,
    ←paired_table_moment_as_binomial]
  ring

def sourcePairedDaughterTable (s : FunctionalCapacity.Site 3 2048) (j : SpeciesId)
    (o : FunctionalCapacity.Split 3 2048) : ℝ :=
  pairedDaughterTable (s.a j).val (o.1 j).val

theorem source_paired_daughter_average (s : FunctionalCapacity.Site 3 2048) (j : SpeciesId) :
    (∑ o : FunctionalCapacity.Split 3 2048,
      (FunctionalCapacity.cf3 (literalSourcePar 0)).ps s o*sourcePairedDaughterTable s j o) =
        2*pairedTableMoment (s.a j).val := by
  unfold sourcePairedDaughterTable
  rw [FunctionalCapacity.cf3_ps_marg (p := literalSourcePar 0) s j
    (fun k _ => pairedDaughterTable (s.a j).val k)]
  rw [binE_paired_daughters]
  ring

end
end P161Formal

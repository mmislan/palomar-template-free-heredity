module

public import P161Formal.SourcePairedSplit

/-! Pointwise complete-division bound with the actual postmark floor test.
The daughters share one split and its complement; no earlier readiness
premise and no independent daughter sampling is introduced. -/

@[expose] public section
namespace P161Formal
open scoped BigOperators
noncomputable section

def sourceUntouchedFor (x : RecoverySource) (i v : SiteId) : ℝ :=
  ∑ k : SiteId, if k = i ∨ k = v then 0 else sourceSitePotential x k

def sourceDaughterPotential (s : FunctionalCapacity.Site 3 2048)
    (o : FunctionalCapacity.Split 3 2048) : ℝ :=
  ∑ j : SpeciesId,
    (strongRecoveryWitness (o.1 j).val (s.R && o.2) +
      strongRecoveryWitness ((s.a j).val-(o.1 j).val) (s.R && !o.2))

theorem sum_delete_pair (u : SiteId → ℝ) (i v : SiteId) (hne : v ≠ i) :
    (∑ k : SiteId, if k = i ∨ k = v then 0 else u k) = (∑ k : SiteId, u k)-u i-u v := by
  have hp (k : SiteId) : (if k = i ∨ k = v then 0 else u k) =
      u k-(if k = i then u i else 0)-(if k = v then u v else 0) := by
    by_cases hi : k = i
    · subst k
      simp [Ne.symm hne]
    · by_cases hv : k = v
      · subst k
        simp [hne]
      · simp [hi,hv]
  simp_rw [hp,Finset.sum_sub_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem source_potential_after_division (x : RecoverySource) (i v : SiteId)
    (k : Option SpeciesId) (o : FunctionalCapacity.Split 3 2048) (hne : v ≠ i) :
    sourcePotential strongRecoveryWitness
      (CTMCHeredity20261019.CF3Marked.divisionNext (literalSourcePar 0) x i k o v) =
        sourceUntouchedFor x i v +
          sourceDaughterPotential ((FunctionalCapacity.cf3 (literalSourcePar 0)).td (x i) k) o := by
  unfold sourceUntouchedFor
  rw [sum_delete_pair (sourceSitePotential x) i v hne]
  unfold sourcePotential CTMCHeredity20261019.CF3Marked.divisionNext
  rw [FunctionalCapacity.sum_update_apply
    (fun (s : FunctionalCapacity.Site 3 2048) =>
      ∑ j : SpeciesId, strongRecoveryWitness (s.a j).val s.R)
    (Function.update x i ((FunctionalCapacity.cf3 (literalSourcePar 0)).d1
      ((FunctionalCapacity.cf3 (literalSourcePar 0)).td (x i) k) o)) v
    ((FunctionalCapacity.cf3 (literalSourcePar 0)).merge (x v)
      ((FunctionalCapacity.cf3 (literalSourcePar 0)).d2
        ((FunctionalCapacity.cf3 (literalSourcePar 0)).td (x i) k) o))]
  rw [FunctionalCapacity.sum_update_apply
    (fun (s : FunctionalCapacity.Site 3 2048) =>
      ∑ j : SpeciesId, strongRecoveryWitness (s.a j).val s.R) x i
    ((FunctionalCapacity.cf3 (literalSourcePar 0)).d1
      ((FunctionalCapacity.cf3 (literalSourcePar 0)).td (x i) k) o)]
  rw [Function.update_of_ne hne]
  cases k <;> simp [sourceSitePotential,sourceDaughterPotential,FunctionalCapacity.cf3,
    FunctionalCapacity.Site.comp,Finset.sum_add_distrib]
  all_goals ring

theorem source_division_pair_floors (x : RecoverySource) (i v : SiteId)
    (k : Option SpeciesId) (o : FunctionalCapacity.Split 3 2048) (hne : v ≠ i)
    (hlive : recoverySourceLive
      (CTMCHeredity20261019.CF3Marked.divisionNext (literalSourcePar 0) x i k o v))
    (j : SpeciesId) : 16 ≤ (o.1 j).val ∧ 16 ≤ ((x i).a j).val-(o.1 j).val := by
  constructor
  · have h := hlive.1 i j True.intro
    cases k <;> simpa [CTMCHeredity20261019.CF3Marked.divisionNext,FunctionalCapacity.cf3,
      hne,Ne.symm hne] using h
  · have h := hlive.1 v j True.intro
    cases k <;> simpa [CTMCHeredity20261019.CF3Marked.divisionNext,FunctionalCapacity.cf3,
      FunctionalCapacity.Site.comp] using h

theorem source_killed_division_pointwise (x : RecoverySource) (i v : SiteId)
    (k : Option SpeciesId) (o : FunctionalCapacity.Split 3 2048) (hne : v ≠ i) :
    killedRecoveryPotential
      (CTMCHeredity20261019.CF3Marked.divisionNext (literalSourcePar 0) x i k o v) ≤
        sourceUntouchedFor x i v +
          ∑ j : SpeciesId, sourcePairedDaughterTable
            ((FunctionalCapacity.cf3 (literalSourcePar 0)).td (x i) k) j o := by
  classical
  let y := CTMCHeredity20261019.CF3Marked.divisionNext (literalSourcePar 0) x i k o v
  by_cases hlive : recoverySourceLive y
  · rw [show killedRecoveryPotential y = sourcePotential strongRecoveryWitness y by
      simp only [killedRecoveryPotential,ite_eq_left hlive]]
    rw [source_potential_after_division x i v k o hne]
    apply add_le_add le_rfl
    unfold sourceDaughterPotential
    apply Finset.sum_le_sum
    intro j _
    obtain ⟨hf1,hf2⟩ := source_division_pair_floors x i v k o hne hlive j
    have hcounts : ((FunctionalCapacity.cf3 (literalSourcePar 0)).td (x i) k).a = (x i).a := by
      cases k <;> rfl
    have hb1 : (o.1 j).val ≤ 2048 := by have h := (o.1 j).isLt; omega
    have hb2 : ((x i).a j).val-(o.1 j).val ≤ 2048 := by
      have h : ((x i).a j).val < 2049 := ((x i).a j).isLt
      omega
    have hfirst := (strong_table_comparison (o.1 j).val
      (((FunctionalCapacity.cf3 (literalSourcePar 0)).td (x i) k).R && o.2) hf1 hb1).2
    have hsecond := (strong_table_comparison (((x i).a j).val-(o.1 j).val)
      (((FunctionalCapacity.cf3 (literalSourcePar 0)).td (x i) k).R && !o.2) hf2 hb2).2
    simp only [sourcePairedDaughterTable,pairedDaughterTable,hcounts,
      ite_eq_left (show 16 ≤ (o.1 j).val ∧ 16 ≤ ((x i).a j).val-(o.1 j).val from ⟨hf1,hf2⟩)]
    exact add_le_add hfirst hsecond
  · rw [show killedRecoveryPotential y = 0 by
      simp only [killedRecoveryPotential,ite_eq_right hlive]]
    apply add_nonneg
    · apply Finset.sum_nonneg
      intro l _
      split_ifs
      · exact le_rfl
      · exact source_site_potential_nonnegative x l
    · apply Finset.sum_nonneg
      intro j _
      exact paired_daughter_table_nonnegative _ _

end
end P161Formal

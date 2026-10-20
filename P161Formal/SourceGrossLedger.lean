module

public import P161Formal.SourceStockSupport

/-! One cumulative physical fuel/precursor ledger on a raw complete-mark fold.
Support is explicit here and is discharged by the actual source law. The
prefix fuel identity pays the initial inventory once, including victim losses. -/

set_option autoImplicit false
@[expose] public section
namespace P161Formal
open HybridCTMC HybridCTMC.Kernel CTMCHeredity20261019
open CF3Marked CF3RawPathLift
open scoped BigOperators Classical
noncomputable section

def sourceMarkAllowed (seed : ℝ) (x : SourceState (literalSourcePar seed))
    (m : Option (Mark (literalSourcePar seed))) : Prop :=
  ∀ r : Mark (literalSourcePar seed), m = some r → 0 < sourceIntensity (literalSourcePar seed) x r

theorem source_mark_fuel_balance (seed : ℝ) (hseed : 0 ≤ seed)
    (x : SourceState (literalSourcePar seed)) (m : Option (Mark (literalSourcePar seed)))
    (hm : sourceMarkAllowed seed x m) :
    sourceFuelCount (sourceProposalNext (literalSourcePar seed) x m)+
      sourceMarkConsumed m+sourceMarkVictimFuel x m = sourceFuelCount x+sourceMarkFeed m := by
  cases m with
  | none => simp only [sourceProposalNext,sourceMarkConsumed,sourceMarkVictimFuel,sourceMarkFeed,Nat.add_zero]
  | some r =>
      have hp := hm r rfl
      cases r with
      | inl ik =>
          rcases ik with ⟨i,k⟩
          simpa only [sourceProposalNext,sourceMarkConsumed,sourceMarkVictimFuel,sourceMarkFeed,Nat.add_zero]
            using source_chemical_fuel_balance seed x i k hp
      | inr d =>
          rcases d with ⟨i,k,o,v⟩
          simpa only [sourceProposalNext,sourceMarkConsumed,sourceMarkVictimFuel,sourceMarkFeed,Nat.add_zero]
            using source_division_fuel_balance seed hseed x i v k o hp

theorem source_mark_birth_le_consumed (seed : ℝ) (m : Option (Mark (literalSourcePar seed))) :
    sourceMarkBirths m ≤ sourceMarkConsumed m := by
  cases m with
  | none => simp [sourceMarkBirths,sourceMarkConsumed]
  | some r =>
      cases r with
      | inl ik =>
          rcases ik with ⟨i,k⟩
          cases k with
          | inl tj =>
              rcases tj with ⟨t,j⟩
              by_cases ht : t = 1 <;> simp [sourceMarkBirths,sourceMarkConsumed,sourceChemConsumed,ht]
          | inr b => cases b <;> simp [sourceMarkBirths,sourceMarkConsumed,sourceChemConsumed]
      | inr d => simp [sourceMarkBirths,sourceMarkConsumed]

theorem source_mark_victim_fuel_le_division (seed : ℝ) (x : SourceState (literalSourcePar seed))
    (m : Option (Mark (literalSourcePar seed))) :
    sourceMarkVictimFuel x m ≤ sourceMarkDivision m := by
  cases m with
  | none => simp [sourceMarkVictimFuel,sourceMarkDivision]
  | some r =>
      cases r with
      | inl ik => simp [sourceMarkVictimFuel,sourceMarkDivision]
      | inr d =>
          rcases d with ⟨i,k,o,v⟩
          cases hr : (x v).R <;> simp [sourceMarkVictimFuel,sourceMarkDivision,bitFuel,hr]

def sourcePrefixCount (seed : ℝ) (f : Option (Mark (literalSourcePar seed)) → ℕ)
    (w : MarkedPath (literalSourcePar seed)) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, f (w (k+1)).2.2

def sourcePrefixVictimFuel (seed : ℝ) (x : SourceState (literalSourcePar seed))
    (w : MarkedPath (literalSourcePar seed)) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, sourceMarkVictimFuel (rawAt (literalSourcePar seed) x w k) (w (k+1)).2.2

def sourceRawSupported (seed : ℝ) (x : SourceState (literalSourcePar seed))
    (w : MarkedPath (literalSourcePar seed)) : Prop :=
  ∀ n : ℕ, sourceMarkAllowed seed (rawAt (literalSourcePar seed) x w n) (w (n+1)).2.2

theorem source_raw_prefix_fuel_balance (seed : ℝ) (hseed : 0 ≤ seed)
    (x : SourceState (literalSourcePar seed)) (w : MarkedPath (literalSourcePar seed))
    (hw : sourceRawSupported seed x w) (n : ℕ) :
    sourceFuelCount x+sourcePrefixCount seed sourceMarkFeed w n =
      sourceFuelCount (rawAt (literalSourcePar seed) x w n)+
        sourcePrefixCount seed sourceMarkConsumed w n+sourcePrefixVictimFuel seed x w n := by
  have hstep (k : ℕ) :
      sourceFuelCount (rawAt (literalSourcePar seed) x w (k+1))+
        sourceMarkConsumed (w (k+1)).2.2+
        sourceMarkVictimFuel (rawAt (literalSourcePar seed) x w k) (w (k+1)).2.2 =
      sourceFuelCount (rawAt (literalSourcePar seed) x w k)+sourceMarkFeed (w (k+1)).2.2 := by
    rw [rawAt_succ]
    exact source_mark_fuel_balance seed hseed _ _ (hw k)
  exact fuel_history_balance
    (fun k => sourceFuelCount (rawAt (literalSourcePar seed) x w k))
    (fun k => sourceMarkFeed (w (k+1)).2.2)
    (fun k => sourceMarkConsumed (w (k+1)).2.2)
    (fun k => sourceMarkVictimFuel (rawAt (literalSourcePar seed) x w k) (w (k+1)).2.2) hstep n

theorem source_prefix_birth_le_consumed (seed : ℝ) (w : MarkedPath (literalSourcePar seed)) (n : ℕ) :
    sourcePrefixCount seed sourceMarkBirths w n ≤ sourcePrefixCount seed sourceMarkConsumed w n :=
  Finset.sum_le_sum (fun k _ => source_mark_birth_le_consumed seed (w (k+1)).2.2)

theorem source_prefix_victim_fuel_le_divisions (seed : ℝ) (x : SourceState (literalSourcePar seed))
    (w : MarkedPath (literalSourcePar seed)) (n : ℕ) :
    sourcePrefixVictimFuel seed x w n ≤ sourcePrefixCount seed sourceMarkDivision w n :=
  Finset.sum_le_sum (fun k _ => source_mark_victim_fuel_le_division seed
    (rawAt (literalSourcePar seed) x w k) (w (k+1)).2.2)

theorem source_prefix_gross_caps (seed : ℝ) (hseed : 0 ≤ seed)
    (x : SourceState (literalSourcePar seed)) (w : MarkedPath (literalSourcePar seed))
    (hw : sourceRawSupported seed x w) (n : ℕ)
    (ha : sourcePrefixCount seed sourceMarkFeed w n ≤ 800000000)
    (he : sourcePrefixCount seed sourceMarkSeeds w n ≤ 5000)
    (hd : sourcePrefixCount seed sourceMarkDivision w n ≤ 1200) :
    sourcePrefixCount seed sourceMarkConsumed w n+sourcePrefixVictimFuel seed x w n ≤ 800000004 ∧
    sourcePrefixCount seed sourceMarkBirths w n+sourcePrefixCount seed sourceMarkSeeds w n ≤ 800005004 ∧
    sourcePrefixVictimFuel seed x w n ≤ 1200 ∧
    3*2048*sourcePrefixCount seed sourceMarkDivision w n ≤ 7372800 := by
  have hb := source_raw_prefix_fuel_balance seed hseed x w hw n
  have hi : sourceFuelCount x ≤ 4 := total_fuel_at_most_four _
  have hbirth := source_prefix_birth_le_consumed seed w n
  have hvictim := source_prefix_victim_fuel_le_divisions seed x w n
  omega

end
end P161Formal

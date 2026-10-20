module

public import P161Formal.SourceFuelTilt

/-! Physical unit debits for every positive-rate source mark. A division installs
both complementary daughters, and its victim fuel is lost once. No service or
phase boundary supplies fuel or resets a gross counter. -/

set_option autoImplicit false

@[expose] public section
namespace P161Formal
open CTMCHeredity20261019 CF3Marked
open scoped BigOperators Classical
noncomputable section

def sourceChemFeed : FunctionalCapacity.Chem 3 → ℕ
  | Sum.inr false => 1
  | _ => 0

def sourceChemConsumed : FunctionalCapacity.Chem 3 → ℕ
  | Sum.inl (t,_) => if t = 1 ∨ t = 2 ∨ t = 4 then 1 else 0
  | Sum.inr b => if b then 1 else 0

def sourceMarkFeed {seed : ℝ} : Option (Mark (literalSourcePar seed)) → ℕ
  | some (Sum.inl (_,k)) => sourceChemFeed k
  | _ => 0

def sourceMarkConsumed {seed : ℝ} : Option (Mark (literalSourcePar seed)) → ℕ
  | some (Sum.inl (_,k)) => sourceChemConsumed k
  | some (Sum.inr (_,k,_)) => if k.isSome then 1 else 0
  | none => 0

def sourceMarkVictimFuel {seed : ℝ} (x : SourceState (literalSourcePar seed)) :
    Option (Mark (literalSourcePar seed)) → ℕ
  | some (Sum.inr (_,_,_,v)) => bitFuel (x v).R
  | _ => 0

def sourceMarkDivision {seed : ℝ} : Option (Mark (literalSourcePar seed)) → ℕ
  | some (Sum.inr _) => 1
  | _ => 0

def sourceMarkSeeds {seed : ℝ} : Option (Mark (literalSourcePar seed)) → ℕ
  | some (Sum.inl (_,Sum.inl (t,_))) => if t = 0 then 1 else 0
  | _ => 0

def sourceMarkBirths {seed : ℝ} : Option (Mark (literalSourcePar seed)) → ℕ
  | some (Sum.inl (_,Sum.inl (t,_))) => if t = 1 then 1 else 0
  | _ => 0

theorem source_fuel_vector_update (seed : ℝ) (x : SourceState (literalSourcePar seed))
    (i : SiteId) (y : FunctionalCapacity.Site 3 2048) :
    (fun j => (Function.update x i y j).R) = Function.update (fun j => (x j).R) i y.R := by
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [h]

theorem source_chemical_bit_balance (seed : ℝ) (x : SourceState (literalSourcePar seed))
    (i : SiteId) (k : FunctionalCapacity.Chem 3)
    (hp : 0 < (FunctionalCapacity.cf3 (literalSourcePar seed)).rc (x i) k) :
    bitFuel ((FunctionalCapacity.cf3 (literalSourcePar seed)).tc (x i) k).R+
      sourceChemConsumed k = bitFuel (x i).R+sourceChemFeed k := by
  cases k with
  | inl tj =>
      rcases tj with ⟨t,j⟩
      fin_cases t <;> cases hr : (x i).R <;>
        norm_num [FunctionalCapacity.cf3,FunctionalCapacity.Site.r,hr,
          sourceChemConsumed,sourceChemFeed,bitFuel] at hp <;>
        norm_num [FunctionalCapacity.cf3,hr,sourceChemConsumed,sourceChemFeed,bitFuel]
  | inr b =>
      cases b <;> cases hr : (x i).R <;>
        norm_num [FunctionalCapacity.cf3,FunctionalCapacity.Site.r,hr,
          sourceChemConsumed,sourceChemFeed,bitFuel] at hp <;>
        norm_num [FunctionalCapacity.cf3,hr,sourceChemConsumed,sourceChemFeed,bitFuel]

theorem source_chemical_fuel_balance (seed : ℝ) (x : SourceState (literalSourcePar seed))
    (i : SiteId) (k : FunctionalCapacity.Chem 3)
    (hp : 0 < sourceIntensity (literalSourcePar seed) x (Sum.inl (i,k))) :
    sourceFuelCount (sourceNext (literalSourcePar seed) x (Sum.inl (i,k)))+
      sourceChemConsumed k = sourceFuelCount x+sourceChemFeed k := by
  have hu := fuel_update_balance (fun j => (x j).R) i
    ((FunctionalCapacity.cf3 (literalSourcePar seed)).tc (x i) k).R
  change totalFuel (Function.update (fun j => (x j).R) i
    ((FunctionalCapacity.cf3 (literalSourcePar seed)).tc (x i) k).R)+bitFuel (x i).R =
      totalFuel (fun j => (x j).R)+
        bitFuel ((FunctionalCapacity.cf3 (literalSourcePar seed)).tc (x i) k).R at hu
  have hb := source_chemical_bit_balance seed x i k hp
  unfold sourceFuelCount
  rw [sourceNext,source_fuel_vector_update]
  have he :
      (totalFuel (Function.update (fun j => (x j).R) i
        ((FunctionalCapacity.cf3 (literalSourcePar seed)).tc (x i) k).R)+sourceChemConsumed k)+bitFuel (x i).R =
      (totalFuel (fun j => (x j).R)+sourceChemFeed k)+bitFuel (x i).R := by
    calc
      _ = (totalFuel (Function.update (fun j => (x j).R) i
          ((FunctionalCapacity.cf3 (literalSourcePar seed)).tc (x i) k).R)+bitFuel (x i).R)+
            sourceChemConsumed k := by ac_rfl
      _ = (totalFuel (fun j => (x j).R)+
          bitFuel ((FunctionalCapacity.cf3 (literalSourcePar seed)).tc (x i) k).R)+sourceChemConsumed k :=
        congrArg (fun n : ℕ => n+sourceChemConsumed k) hu
      _ = totalFuel (fun j => (x j).R)+(bitFuel ((FunctionalCapacity.cf3 (literalSourcePar seed)).tc (x i) k).R+
          sourceChemConsumed k) := Nat.add_assoc _ _ _
      _ = totalFuel (fun j => (x j).R)+(bitFuel (x i).R+sourceChemFeed k) :=
        congrArg (fun n : ℕ => totalFuel (fun j => (x j).R)+n) hb
      _ = _ := by ac_rfl
  exact Nat.add_right_cancel he

theorem source_division_bit_balance (seed : ℝ) (s : FunctionalCapacity.Site 3 2048)
    (k : Option SpeciesId) (o : FunctionalCapacity.Split 3 2048)
    (hp : 0 < (FunctionalCapacity.cf3 (literalSourcePar seed)).rd s k) :
    bitFuel ((FunctionalCapacity.cf3 (literalSourcePar seed)).d1
      ((FunctionalCapacity.cf3 (literalSourcePar seed)).td s k) o).R+
    bitFuel ((FunctionalCapacity.cf3 (literalSourcePar seed)).d2
      ((FunctionalCapacity.cf3 (literalSourcePar seed)).td s k) o).R+
      (if k.isSome then 1 else 0) = bitFuel s.R := by
  cases k <;> cases hr : s.R <;> cases hb : o.2 <;>
    simp_all [FunctionalCapacity.cf3,FunctionalCapacity.Site.r,bitFuel]

theorem source_division_fuel_balance (seed : ℝ) (hseed : 0 ≤ seed)
    (x : SourceState (literalSourcePar seed)) (i v : SiteId)
    (k : Option SpeciesId) (o : FunctionalCapacity.Split 3 2048)
    (hp : 0 < sourceIntensity (literalSourcePar seed) x (Sum.inr (i,k,o,v))) :
    sourceFuelCount (sourceNext (literalSourcePar seed) x (Sum.inr (i,k,o,v)))+
      (if k.isSome then 1 else 0)+bitFuel (x v).R = sourceFuelCount x := by
  have hvi : v ≠ i := by
    intro he
    subst v
    simp [sourceIntensity,outcomeWeight,victimWeight] at hp
  have hrd : 0 < (FunctionalCapacity.cf3 (literalSourcePar seed)).rd (x i) k := by
    change 0 < (FunctionalCapacity.cf3 (literalSourcePar seed)).rd (x i) k*
      outcomeWeight i ((FunctionalCapacity.cf3 (literalSourcePar seed)).td (x i) k) (o,v) at hp
    by_contra hn
    have he := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn)
      (outcomeWeight_nonneg (literal_source_valid seed hseed) i
        ((FunctionalCapacity.cf3 (literalSourcePar seed)).td (x i) k) (o,v))
    exact not_lt_of_ge he hp
  have hb := source_division_bit_balance seed (x i) k o hrd
  have hu := fuel_update_balance (fun j => (x j).R) i
    ((FunctionalCapacity.cf3 (literalSourcePar seed)).d1
      ((FunctionalCapacity.cf3 (literalSourcePar seed)).td (x i) k) o).R
  have hv := fuel_update_balance (Function.update (fun j => (x j).R) i
    ((FunctionalCapacity.cf3 (literalSourcePar seed)).d1
      ((FunctionalCapacity.cf3 (literalSourcePar seed)).td (x i) k) o).R) v
    ((FunctionalCapacity.cf3 (literalSourcePar seed)).d2
      ((FunctionalCapacity.cf3 (literalSourcePar seed)).td (x i) k) o).R
  simp only [Function.update_of_ne hvi] at hv
  unfold sourceFuelCount
  rw [sourceNext,divisionNext,source_fuel_vector_update,source_fuel_vector_update]
  change totalFuel (Function.update (Function.update (fun j => (x j).R) i
    ((FunctionalCapacity.cf3 (literalSourcePar seed)).d1
      ((FunctionalCapacity.cf3 (literalSourcePar seed)).td (x i) k) o).R) v
    ((FunctionalCapacity.cf3 (literalSourcePar seed)).d2
      ((FunctionalCapacity.cf3 (literalSourcePar seed)).td (x i) k) o).R)+_+_ = _
  omega

end
end P161Formal

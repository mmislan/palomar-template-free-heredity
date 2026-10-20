module

public import P161Formal.ModelOperations
public import proofs.CTMCHeredity20261019.CF3Marked

/-! The independently visible contract rates and complete division mark are
identified with the preserved literal CF3 source. No stochastic law or
successful mission is supplied as an interface assumption. -/

@[expose] public section
namespace P161Formal
open scoped BigOperators
noncomputable section

abbrev literalSourcePar (seed : ℝ) : FunctionalCapacity.Par where
  M := 4
  c := 3
  N := 2048
  α := 800
  β := 4000000
  ε := seed

abbrev sourcePopulation {seed : ℝ}
    (x : CTMCHeredity20261019.SourceState (literalSourcePar seed)) : Population where
  count i := (x i).a
  fuel i := (x i).R

theorem literal_source_valid (seed : ℝ) (hseed : 0 ≤ seed) :
    (literalSourcePar seed).Valid := by
  constructor <;> norm_num [literalSourcePar]
  exact hseed

theorem source_common_clock :
    FunctionalCapacity.cf3Rate (literalSourcePar 6) = 93515864 ∧
    FunctionalCapacity.cf3Rate (literalSourcePar 0) = 93515792 := by
  norm_num [FunctionalCapacity.cf3Rate,literalSourcePar]

theorem source_updates_seed_independent (seed1 seed2 : ℝ)
    (x : CTMCHeredity20261019.SourceState (literalSourcePar seed1))
    (m : CTMCHeredity20261019.CF3Marked.Mark (literalSourcePar seed1)) :
    CTMCHeredity20261019.CF3Marked.sourceNext (literalSourcePar seed1) x m =
      CTMCHeredity20261019.CF3Marked.sourceNext (literalSourcePar seed2) x m := by
  cases m with
  | inl q =>
      rcases q with ⟨i,k⟩
      cases k with
      | inl tj => rfl
      | inr b => cases b <;> rfl
  | inr q =>
      rcases q with ⟨i,k,o,v⟩
      cases k <;> rfl

def contractChemicalLabel : ChemicalChannel → SiteId × FunctionalCapacity.Chem 3
  | .seed i j => (i, Sum.inl (0,j))
  | .passive i j => (i, Sum.inl (3,j))
  | .birth i j => (i, Sum.inl (1,j))
  | .activeDeath i j => (i, Sum.inl (2,j))
  | .ordinary i j => (i, Sum.inl (4,j))
  | .recharge i => (i, Sum.inr false)
  | .discharge i => (i, Sum.inr true)

theorem contract_chemical_rate_is_source (t : ℝ)
    (x : CTMCHeredity20261019.SourceState (literalSourcePar (seedCoefficient t)))
    (c : ChemicalChannel) :
    chemicalRate t (sourcePopulation x) c =
      CTMCHeredity20261019.CF3Marked.sourceIntensity
        (literalSourcePar (seedCoefficient t)) x (Sum.inl (contractChemicalLabel c)) := by
  cases c <;>
    simp [chemicalRate,contractChemicalLabel,copies,fueled,
      CTMCHeredity20261019.CF3Marked.sourceIntensity,FunctionalCapacity.cf3,
      FunctionalCapacity.Site.u,FunctionalCapacity.Site.r,literalSourcePar] <;>
      (try split_ifs) <;> norm_num; ring

theorem contract_division_rate_is_source {seed : ℝ}
    (x : CTMCHeredity20261019.SourceState (literalSourcePar seed))
    (i : SiteId) (k : Option SpeciesId) :
    divisionRate (sourcePopulation x) i k =
      (FunctionalCapacity.cf3 (literalSourcePar seed)).rd (x i) k := by
  cases k <;>
    simp [divisionRate,copies,fueled,FunctionalCapacity.cf3,
      FunctionalCapacity.Site.u,FunctionalCapacity.Site.r,literalSourcePar]
  split_ifs <;> simp_all

theorem contract_complete_chemical_is_source {seed : ℝ}
    (x : CTMCHeredity20261019.SourceState (literalSourcePar seed)) (k : ChemicalChannel) :
    sourcePopulation (CTMCHeredity20261019.CF3Marked.sourceNext (literalSourcePar seed) x
      (Sum.inl (contractChemicalLabel k))) = afterChemical (sourcePopulation x) k := by
  apply population_ext
  · intro i j
    cases k <;>
      simp [sourcePopulation,CTMCHeredity20261019.CF3Marked.sourceNext,
        contractChemicalLabel,FunctionalCapacity.cf3,afterChemical,chemicalCountsAfter,
        changeCountAt,incrementCopies,decrementCopies,FunctionalCapacity.Site.inc,
        FunctionalCapacity.Site.dec,literalSourcePar,Function.update_apply] <;>
        (try split_ifs) <;> simp_all
  · intro i
    cases k <;>
      simp [sourcePopulation,CTMCHeredity20261019.CF3Marked.sourceNext,
        contractChemicalLabel,FunctionalCapacity.cf3,afterChemical,chemicalFuelAfter,
        literalSourcePar,Function.update_apply] <;> (try split_ifs) <;> simp_all

def contractSourceSplit {seed : ℝ}
    (x : CTMCHeredity20261019.SourceState (literalSourcePar seed))
    (m : DivisionMark (sourcePopulation x)) : FunctionalCapacity.Split 3 2048 :=
  ((fun j => ⟨m.first j, lt_of_le_of_lt (m.bounded j) ((x m.parent).a j).isLt⟩),m.fuelBit)

def contractSourceDivisionLabel {seed : ℝ}
    (x : CTMCHeredity20261019.SourceState (literalSourcePar seed))
    (m : DivisionMark (sourcePopulation x)) :
    CTMCHeredity20261019.CF3Marked.Mark (literalSourcePar seed) :=
  Sum.inr (m.parent,(m.trigger,(contractSourceSplit x m,m.victim)))

theorem contract_division_mark_rate_is_source {seed : ℝ}
    (x : CTMCHeredity20261019.SourceState (literalSourcePar seed))
    (m : DivisionMark (sourcePopulation x)) :
    divisionMarkRate (sourcePopulation x) m =
      CTMCHeredity20261019.CF3Marked.sourceIntensity (literalSourcePar seed) x
        (contractSourceDivisionLabel x m) := by
  rw [divisionMarkRate,contract_division_rate_is_source]
  cases h : m.trigger <;>
    simp [contractSourceDivisionLabel,contractSourceSplit,
      CTMCHeredity20261019.CF3Marked.sourceIntensity,
      CTMCHeredity20261019.CF3Marked.outcomeWeight,
      CTMCHeredity20261019.CF3Marked.victimWeight,m.distinct,
      FunctionalCapacity.cf3,FunctionalCapacity.Site.u,FunctionalCapacity.Site.r,
      literalSourcePar,sourcePopulation,h] <;> (try split_ifs) <;> norm_num <;> ring

theorem contract_complete_division_is_source {seed : ℝ}
    (x : CTMCHeredity20261019.SourceState (literalSourcePar seed))
    (m : DivisionMark (sourcePopulation x)) :
    sourcePopulation (CTMCHeredity20261019.CF3Marked.sourceNext (literalSourcePar seed) x
      (contractSourceDivisionLabel x m)) = afterDivision (sourcePopulation x) m := by
  cases h : m.trigger <;>
    simp only [contractSourceDivisionLabel,CTMCHeredity20261019.CF3Marked.sourceNext,
      CTMCHeredity20261019.CF3Marked.divisionNext]
  all_goals
    unfold sourcePopulation afterDivision
    congr 1
    · funext i j
      by_cases hv : i = m.victim
      · subst i
        simp [FunctionalCapacity.cf3,contractSourceSplit,secondDaughterCount,
          sourcePopulation,FunctionalCapacity.Site.comp,h]
      · by_cases hp : i = m.parent
        · subst i
          simp [FunctionalCapacity.cf3,contractSourceSplit,sourcePopulation,
            hv,h]
        · simp [FunctionalCapacity.cf3,hv,hp]
    · funext i
      by_cases hv : i = m.victim
      · subst i
        simp [FunctionalCapacity.cf3,contractSourceSplit,divisionFuel,
          sourcePopulation,h]
      · by_cases hp : i = m.parent
        · subst i
          simp [FunctionalCapacity.cf3,contractSourceSplit,divisionFuel,
            sourcePopulation,hv,h]
        · simp [FunctionalCapacity.cf3,hv,hp]

end
end P161Formal

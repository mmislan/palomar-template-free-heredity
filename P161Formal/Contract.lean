module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega

/-!
An independent, explicit statement-development interface for the literal P161
mission. The rates, complete division marks, observed floors, fixed-grid service,
renewal event and budgets are visible here. No desired probability estimate or
source-law axiom is introduced. A stochastic realization and source equivalence
must still be constructed before a Challenge/Solution can be completed.
-/

@[expose] public section

namespace P161Formal

open scoped BigOperators
noncomputable section

abbrev SiteId := Fin 4
abbrev SpeciesId := Fin 3

structure Population where
  count : SiteId → SpeciesId → Fin 2049
  fuel : SiteId → Bool

def seedCoefficient (t : ℝ) : ℝ := if t < 30 then 6 else 0

inductive ChemicalChannel where
  | seed (i : SiteId) (j : SpeciesId)
  | passive (i : SiteId) (j : SpeciesId)
  | birth (i : SiteId) (j : SpeciesId)
  | activeDeath (i : SiteId) (j : SpeciesId)
  | ordinary (i : SiteId) (j : SpeciesId)
  | recharge (i : SiteId)
  | discharge (i : SiteId)

def fueled (x : Population) (i : SiteId) : ℝ := if x.fuel i then 1 else 0
def copies (x : Population) (i : SiteId) (j : SpeciesId) : ℝ := (x.count i j).val

def chemicalRate (t : ℝ) (x : Population) : ChemicalChannel → ℝ
  | .seed i j => seedCoefficient t * (1 - copies x i j / 2048)
  | .passive i j => copies x i j
  | .birth i j => 800 * fueled x i * copies x i j * (1 - copies x i j / 2048)
  | .activeDeath i j => 400 * fueled x i * copies x i j
  | .ordinary i j => 4000000 * fueled x i * copies x i j / 2048
  | .recharge i => 4000000 * (1 - fueled x i)
  | .discharge i => 4000000 * fueled x i

/-- `none` is basal; `some j` is the fuel-consuming, j-credited division. -/
def divisionRate (x : Population) (i : SiteId) : Option SpeciesId → ℝ
  | none => 1
  | some j => fueled x i * copies x i j / 2048

structure DivisionMark (x : Population) where
  parent : SiteId
  victim : SiteId
  distinct : victim ≠ parent
  trigger : Option SpeciesId
  first : SpeciesId → ℕ
  bounded : ∀ j, first j ≤ (x.count parent j).val
  fuelBit : Bool

/-- One fair bit, a uniform distinct victim, and three independent binomial
allocations. Sisters use this same vector and its complement. -/
def divisionMarkRate (x : Population) (m : DivisionMark x) : ℝ :=
  divisionRate x m.parent m.trigger / 3 * (1 / 2) *
    ∏ j, (((x.count m.parent j).val.choose (m.first j) : ℝ) /
      2 ^ (x.count m.parent j).val)

def secondDaughterCount (x : Population) (m : DivisionMark x) (j : SpeciesId) : ℕ :=
  (x.count m.parent j).val - m.first j

def divisionFuel (x : Population) (m : DivisionMark x) : Bool × Bool :=
  let retained := x.fuel m.parent && m.trigger.isNone
  (retained && m.fuelBit, retained && !m.fuelBit)

/-- Both daughters overwrite the parent and victim in one complete mark. -/
def afterDivision (x : Population) (m : DivisionMark x) : Population where
  count := Function.update
    (Function.update x.count m.parent (fun j =>
      ⟨m.first j, lt_of_le_of_lt (m.bounded j) (x.count m.parent j).isLt⟩))
    m.victim (fun j =>
      ⟨secondDaughterCount x m j,
        lt_of_le_of_lt (Nat.sub_le _ _) (x.count m.parent j).isLt⟩)
  fuel := Function.update
    (Function.update x.fuel m.parent (divisionFuel x m).1)
    m.victim (divisionFuel x m).2

def prepared (x : Population) : Prop :=
  ∀ i j, j.val < 2 → 512 ≤ (x.count i j).val

def ready512 (x : Population) : Prop := ∀ i j, 512 ≤ (x.count i j).val

def floorFor (x : Population) (species : SpeciesId → Prop) : Prop :=
  ∀ i j, species j → 16 ≤ (x.count i j).val

/-- Actual complete postmark floors imply both daughters and the parent's32
floor. No earlier Ready512 premise or independent-sister assumption is used. -/
theorem actual_complementary_inheritance (x : Population) (m : DivisionMark x)
    (hfloor : floorFor (afterDivision x m) (fun _ => True)) (j : SpeciesId) :
    16 ≤ m.first j ∧ 16 ≤ secondDaughterCount x m j ∧
    32 ≤ (x.count m.parent j).val := by
  have hfirst : 16 ≤ m.first j := by
    simpa [afterDivision, m.distinct, Ne.symm m.distinct] using
      hfloor m.parent j True.intro
  have hsecond : 16 ≤ secondDaughterCount x m j := by
    simpa [afterDivision] using hfloor m.victim j True.intro
  refine ⟨hfirst, hsecond, ?_⟩
  have hsplit := m.bounded j
  unfold secondDaughterCount at hsecond
  omega

/-- Observations of a right-continuous complete-mark history. A future
realization must prove that these are its actual counters and state path. -/
structure MissionObservations where
  state : ℝ → Population
  credits : ℝ → SiteId → SpeciesId → ℕ
  initiatingDivisions : ℝ → SiteId → ℕ
  feed : ℝ → ℕ
  seeds : ℝ → ℕ
  consumedFuel : ℝ → ℕ
  precursors : ℝ → ℕ
  divisions : ℝ → ℕ
  victimSlots : ℝ → ℕ
  victimFuel : ℝ → ℕ
  isDivision : ℝ → Prop

def fixedGridService (o : MissionObservations) : Prop :=
  (∀ (n : Fin 300) i j, j.val < 2 →
    o.credits ((n.val : ℝ) / 10) i j + 500 ≤
      o.credits (((n.val : ℝ) + 1) / 10) i j) ∧
  (∀ (n : Fin 300) i j,
    o.credits (30 + (n.val : ℝ) / 10) i j + 500 ≤
      o.credits (30 + ((n.val : ℝ) + 1) / 10) i j)

def protectedFloors (o : MissionObservations) : Prop :=
  (∀ t, 0 ≤ t → t ≤ 30 → floorFor (o.state t) (fun j => j.val < 2)) ∧
  (∀ t, 30 ≤ t → t ≤ 60 → floorFor (o.state t) (fun _ => True))

/-- An attained first hit, including the complete state at its starting mark. -/
def firstReadyAtOrAfter (o : MissionObservations) (start hit : ℝ) : Prop :=
  start ≤ hit ∧ ready512 (o.state hit) ∧
    ∀ t, start ≤ t → t < hit → ¬ready512 (o.state t)

/-- State-null divisions count. The division is strictly after the ready hit. -/
def firstDivisionAfter (o : MissionObservations) (start division : ℝ) : Prop :=
  start < division ∧ o.isDivision division ∧
    ∀ t, start < t → t < division → ¬o.isDivision t

def renewalMission (o : MissionObservations) : Prop :=
  ∃ (τ : Fin 11 → ℝ) (σ : Fin 10 → ℝ),
    firstReadyAtOrAfter o 30 (τ 0) ∧ τ 0 ≤ 30 + 1 / 2 ∧
    (∀ r : Fin 10,
      firstDivisionAfter o (τ r.castSucc) (σ r) ∧
      σ r - τ r.castSucc ≤ 2 ∧
      firstReadyAtOrAfter o (σ r) (τ r.succ) ∧
      τ r.succ - σ r ≤ 1 / 2) ∧
    τ 10 ≤ 111 / 2

def stockMission (o : MissionObservations) : Prop :=
  ∀ t, 0 ≤ t → t ≤ 60 →
    o.feed t ≤ 800000000 ∧ o.seeds t ≤ 5000 ∧
    o.consumedFuel t ≤ 800000004 ∧ o.precursors t ≤ 800005004 ∧
    o.divisions t ≤ 1200 ∧ o.victimSlots t ≤ 7372800 ∧ o.victimFuel t ≤ 1200

def completeMission (o : MissionObservations) : Prop :=
  protectedFloors o ∧ fixedGridService o ∧ renewalMission o ∧ stockMission o ∧
  (∀ i, o.initiatingDivisions 30 i + 5 ≤ o.initiatingDivisions 60 i)

def failureCeiling : ℝ := 4517975690072193 / 10^18

theorem seed_off_at_switch : seedCoefficient 30 = 0 := by norm_num [seedCoefficient]
theorem seed_off_after_switch (t : ℝ) (h : 30 ≤ t) : seedCoefficient t = 0 := by
  simp [seedCoefficient, not_lt.mpr h]

end
end P161Formal

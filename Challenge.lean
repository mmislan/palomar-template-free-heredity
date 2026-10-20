module
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Order.Fin.Basic
public import Mathlib.Probability.CondVar
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.ProbabilityMassFunction.Binomial
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Finiteness
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Measurability
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.InfiniteSum.Order
/-! Independent Challenge: explicit CF3 rates, complementary split, actual
marked clock law, unconditional deterministic seed switch, absorbing finite
stock, and the full 60-time mission. The main result is a Challenge hole.
Only proof obligations may be holes; substantive definitions are fixed. -/
set_option linter.auxLemma false
@[expose] public section
/- Proof-only numeric witnesses retain the names used by the proved source. -/
theorem P161Formal.fixedGridService._proof_1 : (9 + 1).AtLeastTwo := by sorry
theorem P161Formal.failureCeiling._proof_1 : (4517975690072192 + 1).AtLeastTwo := by sorry
theorem CTMCHeredity20261019.canonicalSeedFreeCF3._proof_2 : (3999999 + 1).AtLeastTwo := by sorry
theorem CTMCHeredity20261019.canonicalSeedFreeCF3._proof_1 : (799 + 1).AtLeastTwo := by sorry
theorem CTMCHeredity20261019.V2.SeedSwitch.blockDuration._proof_1 : (9 + 1).AtLeastTwo := by sorry
theorem CTMCHeredity20261019.V2.SeedSwitch.canonicalSeedOnCF3._proof_3 : (5 + 1).AtLeastTwo := by sorry
theorem CTMCHeredity20261019.V2.SeedSwitch.canonicalSeedOnCF3._proof_2 : (3999999 + 1).AtLeastTwo := by sorry
theorem CTMCHeredity20261019.V2.SeedSwitch.canonicalSeedOnCF3._proof_1 : (799 + 1).AtLeastTwo := by sorry
theorem P161Formal.literalSourcePar._proof_2 : (3999999 + 1).AtLeastTwo := by sorry
theorem P161Formal.literalSourcePar._proof_1 : (799 + 1).AtLeastTwo := by sorry
theorem P161Formal.globalSourceDivisionAt._proof_1 : (29 + 1).AtLeastTwo := by sorry
theorem P161Formal.emptyStockPopulation._proof_1 : @NeZero.{0} Nat (@Zero.ofOfNat0.{0} Nat (instOfNatNat (nat_lit 0))) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@OfNat.ofNat.{0} Nat (nat_lit 2048) (instOfNatNat (nat_lit 2048))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by sorry
theorem P161Formal.sourceRealizedObservations._proof_1 : (5 + 1).AtLeastTwo := by sorry
theorem P161Formal.protectedFloors._proof_1 : (59 + 1).AtLeastTwo := by sorry
theorem P161Formal.seedCoefficient._proof_1 : (29 + 1).AtLeastTwo := by sorry
theorem P161Formal.renewalMission._proof_2 : (110 + 1).AtLeastTwo := by sorry
theorem P161Formal.divisionMarkRate._proof_2 : (1 + 1).AtLeastTwo := by sorry
theorem P161Formal.renewalMission._proof_1 : @NeZero.{0} Nat (@Zero.ofOfNat0.{0} Nat (instOfNatNat (nat_lit 0))) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by sorry
theorem FunctionalCapacity.cf3._proof_2 : (1 + 1).AtLeastTwo := by sorry
theorem FunctionalCapacity.cf3._proof_1 : @NeZero.{0} Nat (@Zero.ofOfNat0.{0} Nat (instOfNatNat (nat_lit 0))) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by sorry
theorem P161Formal.sourceGlobalInitial._proof_1 : (5 + 1).AtLeastTwo := by sorry
theorem P161Formal.sourceChemConsumed._proof_1 : @NeZero.{0} Nat (@Zero.ofOfNat0.{0} Nat (instOfNatNat (nat_lit 0))) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by sorry
theorem P161Formal.sourceStockStep._proof_1 : (5 + 1).AtLeastTwo := by sorry
namespace P161Formal
open scoped BigOperators
noncomputable section
attribute [local instance] P161Formal.fixedGridService._proof_1 P161Formal.failureCeiling._proof_1 P161Formal.protectedFloors._proof_1 P161Formal.seedCoefficient._proof_1 P161Formal.renewalMission._proof_2 P161Formal.divisionMarkRate._proof_2 P161Formal.renewalMission._proof_1
abbrev SiteId := Fin 4
abbrev SpeciesId := Fin 3
structure Population where
  count : SiteId → SpeciesId → Fin 2049
  fuel : SiteId → Bool
def ready512 (x : Population) : Prop := ∀ i j, 512 ≤ (x.count i j).val
def floorFor (x : Population) (species : SpeciesId → Prop) : Prop :=
  ∀ i j, species j → 16 ≤ (x.count i j).val
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
def firstReadyAtOrAfter (o : MissionObservations) (start hit : ℝ) : Prop :=
  start ≤ hit ∧ ready512 (o.state hit) ∧
    ∀ t, start ≤ t → t < hit → ¬ready512 (o.state t)
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
end
end P161Formal
namespace P161Formal
noncomputable section
open scoped BigOperators
def bitFuel (b : Bool) : ℕ := if b then 1 else 0
end
end P161Formal
namespace FunctionalCapacity
noncomputable section
attribute [local instance] FunctionalCapacity.cf3._proof_2 FunctionalCapacity.cf3._proof_1
open Finset
variable {σ : Type}
structure SiteModel (S ιc ιd ιs : Type) where
  rc : S → ιc → ℝ
  tc : S → ιc → S
  rd : S → ιd → ℝ
  td : S → ιd → S
  ps : S → ιs → ℝ
  d1 : S → ιs → S
  d2 : S → ιs → S
  merge : S → S → S
variable {S ιc ιd ιs : Type} [Fintype ιc] [Fintype ιd] [Fintype ιs]
structure Site (c N : ℕ) where
  a : Fin c → Fin (N + 1)
  R : Bool
  q : Fin c → ℕ
  nd : ℕ
structure Par where
  M : ℕ
  c : ℕ
  N : ℕ
  α : ℝ
  β : ℝ
  ε : ℝ
namespace Site
variable {c N : ℕ}
def u (s : Site c N) (j : Fin c) : ℝ := ((s.a j : ℕ) : ℝ) / N
def r (s : Site c N) : ℝ := if s.R then 1 else 0
def inc (x : Fin (N + 1)) : Fin (N + 1) := ⟨min (x.val + 1) N, by omega⟩
def dec (x : Fin (N + 1)) : Fin (N + 1) := ⟨x.val - 1, by omega⟩
def comp (x k : Fin (N + 1)) : Fin (N + 1) := ⟨x.val - k.val, by omega⟩
end Site
abbrev Chem (c : ℕ) := (Fin 5 × Fin c) ⊕ Bool
abbrev Split (c N : ℕ) := (Fin c → Fin (N + 1)) × Bool
open Site in
def cf3 (p : Par) : SiteModel (Site p.c p.N) (Chem p.c) (Option (Fin p.c)) (Split p.c p.N) where
  rc s k :=
    match k with
    | Sum.inl (t, j) =>
        if t = 0 then p.ε * (1 - s.u j)
        else if t = 1 then p.α * s.r * ((s.a j : ℕ) : ℝ) * (1 - s.u j)
        else if t = 2 then p.α / 2 * s.r * ((s.a j : ℕ) : ℝ)
        else if t = 3 then ((s.a j : ℕ) : ℝ)
        else p.β * s.u j * s.r
    | Sum.inr false => p.β * (1 - s.r)
    | Sum.inr true => p.β * s.r
  tc s k :=
    match k with
    | Sum.inl (t, j) =>
        if t = 0 then { s with a := Function.update s.a j (inc (s.a j)) }
        else if t = 1 then { s with a := Function.update s.a j (inc (s.a j)), R := false }
        else if t = 2 then { s with a := Function.update s.a j (dec (s.a j)), R := false }
        else if t = 3 then { s with a := Function.update s.a j (dec (s.a j)) }
        else { s with R := false, q := Function.update s.q j (s.q j + 1) }
    | Sum.inr false => { s with R := true }
    | Sum.inr true => { s with R := false }
  rd s k :=
    match k with
    | none => 1
    | some j => s.u j * s.r
  td s k :=
    match k with
    | none => { s with nd := s.nd + 1 }
    | some j => { s with R := false, q := Function.update s.q j (s.q j + 1), nd := s.nd + 1 }
  ps s o := (∏ j, ((Nat.choose (s.a j) (o.1 j) : ℕ) : ℝ) / 2 ^ (s.a j : ℕ)) * (1 / 2)
  d1 s o := { s with a := o.1, R := s.R && o.2 }
  d2 s o := { s with a := fun j => comp (s.a j) (o.1 j), R := s.R && !o.2 }
  merge v d := { v with a := d.a, R := d.R }
def cf3Rate (p : Par) : ℝ :=
  p.M * (p.c * (p.ε + p.α * p.N + p.α / 2 * p.N + p.N + p.β) + p.β + (1 + p.c))
end
end FunctionalCapacity
namespace HybridCTMC
open scoped BigOperators
noncomputable section
variable {S : Type*} [Fintype S]
structure Kernel (S : Type*) [Fintype S] where
  weight : S → S → ℝ
  nonneg : ∀ x y, 0 ≤ weight x y
  total : ∀ x, ∑ y, weight x y = 1
namespace Kernel
def pmf (K : Kernel S) (x : S) : PMF S :=
  PMF.ofFintype (fun y => ENNReal.ofReal (K.weight x y)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => K.nonneg x y), K.total]
    simp)
end Kernel
namespace Rates
end Rates
end
end HybridCTMC
namespace HybridCTMC
open scoped BigOperators
noncomputable section
variable {S R : Type*} [Fintype S] [Fintype R]
structure Channels (S R : Type*) where
  next : S → R → S
  propensity : S → R → ℝ
  nonneg : ∀ x r, 0 ≤ propensity x r
namespace Channels
end Channels
end
end HybridCTMC
namespace CTMCHeredity20261019.MarkedUniformization
open scoped BigOperators Classical
noncomputable section
variable {S R : Type} [Fintype R]
def next (C : HybridCTMC.Channels S R) (x : S) : Option R → S
  | none => x
  | some r => C.next x r
def weight (C : HybridCTMC.Channels S R) (Lam : ℝ) (x : S) : Option R → ℝ
  | none => 1 - (∑ r, C.propensity x r) / Lam
  | some r => C.propensity x r / Lam
section FiniteState
variable [Fintype S] [DecidableEq S]
end FiniteState
end
end CTMCHeredity20261019.MarkedUniformization
namespace FunctionalCapacity
noncomputable section
open Finset
structure Par.Valid (p : Par) : Prop where
  hM : 2 ≤ p.M
  hN : 0 < p.N
  hα : 0 ≤ p.α
  hβ : 0 ≤ p.β
  hε : 0 ≤ p.ε
namespace Site
variable {c N : ℕ}
end Site
variable {p : Par}
end
end FunctionalCapacity
namespace CTMCHeredity20261019
noncomputable section
open FunctionalCapacity
abbrev CoreSite (c N : ℕ) := (Fin c → Fin (N + 1)) × Bool
abbrev CoreState (p : Par) := Fin p.M → CoreSite p.c p.N
abbrev SourceState (p : Par) := Fin p.M → Site p.c p.N
instance independentSourceCountable (p : Par) : Countable (SourceState p) := by sorry
def siteProject {c N : ℕ} (s : Site c N) : CoreSite c N := (s.a, s.R)
def siteRepresent {c N : ℕ} (s : CoreSite c N) : Site c N where
  a := s.1
  R := s.2
  q := fun _ => 0
  nd := 0
def coreProject {p : Par} (x : SourceState p) : CoreState p :=
  fun i => siteProject (x i)
def coreRepresent {p : Par} (x : CoreState p) : SourceState p :=
  fun i => siteRepresent (x i)
end
end CTMCHeredity20261019
namespace CTMCHeredity20261019.CF3Marked
open FunctionalCapacity
open scoped BigOperators Classical
noncomputable section
abbrev Mark (p : Par) :=
  (Fin p.M × Chem p.c) ⊕
    (Fin p.M × (Option (Fin p.c) × (Split p.c p.N × Fin p.M)))
def victimWeight (p : Par) (i v : Fin p.M) : ℝ :=
  if v = i then 0 else 1 / ((p.M : ℝ) - 1)
def outcomeWeight {p : Par} (i : Fin p.M) (s : Site p.c p.N)
    (z : Split p.c p.N × Fin p.M) : ℝ :=
  (cf3 p).ps s z.1 * victimWeight p i z.2
def divisionNext (p : Par) (x : SourceState p) (i : Fin p.M)
    (k : Option (Fin p.c)) (o : Split p.c p.N) (v : Fin p.M) : SourceState p :=
  Function.update
    (Function.update x i ((cf3 p).d1 ((cf3 p).td (x i) k) o)) v
    ((cf3 p).merge (x v) ((cf3 p).d2 ((cf3 p).td (x i) k) o))
def sourceNext (p : Par) (x : SourceState p) : Mark p → SourceState p
  | Sum.inl (i, k) => Function.update x i ((cf3 p).tc (x i) k)
  | Sum.inr (i, (k, (o, v))) => divisionNext p x i k o v
def sourceIntensity (p : Par) (x : SourceState p) : Mark p → ℝ
  | Sum.inl (i, k) => (cf3 p).rc (x i) k
  | Sum.inr (i, (k, z)) => (cf3 p).rd (x i) k * outcomeWeight i ((cf3 p).td (x i) k) z
theorem _root_.CTMCHeredity20261019.CF3Marked.coreChannels._proof_1 : ∀ {p : FunctionalCapacity.Par},
  p.Valid →
    ∀ (x : CTMCHeredity20261019.CoreState p) (r : CTMCHeredity20261019.CF3Marked.Mark p),
      0 ≤ CTMCHeredity20261019.CF3Marked.sourceIntensity p (CTMCHeredity20261019.coreRepresent x) r := by sorry
def coreChannels {p : Par} (hp : p.Valid) :
    HybridCTMC.Channels (CoreState p) (Mark p) where
  next x r := coreProject (sourceNext p (coreRepresent x) r)
  propensity x r := sourceIntensity p (coreRepresent x) r
  nonneg := coreChannels._proof_1 hp
end
end CTMCHeredity20261019.CF3Marked
namespace P161Formal
open scoped BigOperators
noncomputable section
attribute [local instance] P161Formal.literalSourcePar._proof_2 P161Formal.literalSourcePar._proof_1
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
end
end P161Formal
set_option autoImplicit false
namespace P161Formal
open CTMCHeredity20261019 CF3Marked
open scoped BigOperators Classical
noncomputable section
attribute [local instance] P161Formal.sourceChemConsumed._proof_1
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
end
end P161Formal
namespace HybridCTMC
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
namespace Kernel
def clockStep (K : HybridCTMC.Kernel S) (Λ : ℝ) (x : S) : Measure (ℝ × S) :=
  (expMeasure Λ).prod (K.pmf x).toMeasure
end Kernel
namespace Rates
variable [DecidableEq S]
end Rates
end
end HybridCTMC
namespace HybridCTMC
open MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators
noncomputable section
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
namespace Kernel
def clockKernel (K : HybridCTMC.Kernel S) (Λ : ℝ) : ProbabilityTheory.Kernel S (ℝ × S) where
  toFun := K.clockStep Λ
  measurable' := measurable_of_countable _
def eventKernel (K : HybridCTMC.Kernel S) (Λ : ℝ) (n : ℕ) :
    ProbabilityTheory.Kernel (Π _ : Finset.Iic n, ℝ × S) (ℝ × S) :=
  (K.clockKernel Λ).comap (fun w => (w ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2) (by fun_prop)
theorem eventKernel_markov (K : HybridCTMC.Kernel S) {Λ : ℝ} (hΛ : 0 < Λ) (n : ℕ) :
    IsMarkovKernel (K.eventKernel Λ n) := by sorry
def eventLaw (K : HybridCTMC.Kernel S) (Λ : ℝ) (hΛ : 0 < Λ) (x : S) :
    Measure (ℕ → ℝ × S) := by
  let := K.eventKernel_markov hΛ
  exact ProbabilityTheory.Kernel.trajMeasure (Measure.dirac (0, x)) (K.eventKernel Λ)
end Kernel
end
end HybridCTMC
namespace HybridCTMC
open MeasureTheory ProbabilityTheory Preorder Set
open scoped BigOperators
noncomputable section
namespace HoldingTime
end HoldingTime
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
namespace Kernel
def arrivalTime (n : ℕ) (w : ℕ → ℝ × S) : ℝ :=
  ∑ i ∈ Finset.range n, max 0 (w (i+1)).1
end Kernel
end
end HybridCTMC
namespace CTMCHeredity20261019.MarkedKernel
open MeasureTheory
open scoped BigOperators Classical
noncomputable section
variable {S R : Type} [Fintype S] [Fintype R]
theorem _root_.CTMCHeredity20261019.MarkedKernel.kernel._proof_1 : ∀ {S R : Type} [inst : Fintype R] (C : HybridCTMC.Channels S R) {Lam : ℝ},
  0 < Lam →
    (∀ (x : S), ∑ r, C.propensity x r ≤ Lam) →
      ∀ (z y : S × Option R),
        0 ≤
          if y.1 = CTMCHeredity20261019.MarkedUniformization.next C z.1 y.2 then
            CTMCHeredity20261019.MarkedUniformization.weight C Lam z.1 y.2
          else 0 := by sorry
theorem _root_.CTMCHeredity20261019.MarkedKernel.kernel._proof_2 : ∀ {S R : Type} [inst : Fintype S] [inst_1 : Fintype R] (C : HybridCTMC.Channels S R) {Lam : ℝ} (z : S × Option R),
  (∑ y : S × Option R,
      if y.1 = CTMCHeredity20261019.MarkedUniformization.next C z.1 y.2 then
        CTMCHeredity20261019.MarkedUniformization.weight C Lam z.1 y.2
      else 0) =
    1 := by sorry
def kernel (C : HybridCTMC.Channels S R) {Lam : ℝ} (hLam : 0 < Lam)
    (bound : ∀ x, ∑ r, C.propensity x r ≤ Lam) :
    HybridCTMC.Kernel (S × Option R) where
  weight z y :=
    if y.1 = MarkedUniformization.next C z.1 y.2
    then MarkedUniformization.weight C Lam z.1 y.2 else 0
  nonneg z y := kernel._proof_1 C hLam bound z y
  total z := kernel._proof_2 C z
section Timed
variable [MeasurableSpace (S × Option R)] [MeasurableSingletonClass (S × Option R)]
end Timed
end
end CTMCHeredity20261019.MarkedKernel
namespace CTMCHeredity20261019
open MeasureTheory FunctionalCapacity
open scoped BigOperators Classical
noncomputable section
attribute [local instance] CTMCHeredity20261019.canonicalSeedFreeCF3._proof_2 CTMCHeredity20261019.canonicalSeedFreeCF3._proof_1
def canonicalSeedFreeCF3 : Par := ⟨4, 3, 2048, 800, 4000000, 0⟩
end
end CTMCHeredity20261019
namespace CTMCHeredity20261019.CF3MarkedKernel
open FunctionalCapacity MeasureTheory CF3Marked
open scoped BigOperators Classical
noncomputable section
abbrev State (p : Par) := CoreState p × Option (Mark p)
theorem rate_positive {p : Par} (hp : p.Valid) : 0 < cf3Rate p := by sorry
theorem core_channel_bound {p : Par} (hp : p.Valid) (x : CoreState p) :
    ∑ r, (coreChannels hp).propensity x r ≤ cf3Rate p := by sorry
def kernel {p : Par} (hp : p.Valid) : HybridCTMC.Kernel (State p) :=
  MarkedKernel.kernel (coreChannels hp) (rate_positive hp) (core_channel_bound hp)
local instance (p : Par) : MeasurableSpace (State p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (State p) := ⟨fun _ => trivial⟩
def eventLaw {p : Par} (hp : p.Valid) (x : CoreState p) (old : Option (Mark p)) :
    Measure (ℕ → ℝ × State p) :=
  (kernel hp).eventLaw (cf3Rate p) (rate_positive hp) (x, old)
end
end CTMCHeredity20261019.CF3MarkedKernel
namespace HybridCTMC
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical
noncomputable section
namespace Kernel
variable {S : Type*} [Fintype S]
def clockIndex (t : ℝ) (w : ℕ → ℝ × S) : ℕ :=
  if h : ∃ n, t < arrivalTime n w then Nat.find h-1 else 0
def timedState (t : ℝ) (w : ℕ → ℝ × S) : S := (w (clockIndex t w)).2
variable [MeasurableSpace S] [MeasurableSingletonClass S] [StandardBorelSpace S]
end Kernel
end
end HybridCTMC
namespace CTMCHeredity20261019.CF3RawPathLift
noncomputable section
open FunctionalCapacity MeasureTheory ProbabilityTheory HybridCTMC.Kernel CF3Marked
open scoped Classical
abbrev MarkedPath (p : Par) := ℕ → ℝ × CF3MarkedKernel.State p
def sourceProposalNext (p : Par) (x : SourceState p) : Option (Mark p) → SourceState p
  | none => x
  | some r => sourceNext p x r
def rawAt (p : Par) (x : SourceState p) (w : MarkedPath p) : ℕ → SourceState p
  | 0 => x
  | n + 1 => sourceProposalNext p (rawAt p x w n) (w (n + 1)).2.2
def rawSequence (p : Par) (x : SourceState p) (w : MarkedPath p) : ℕ → ℝ × SourceState p :=
  fun n => ((w n).1, rawAt p x w n)
local instance (p : Par) : MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (CF3MarkedKernel.State p) := ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (Option (Mark p)) := ⊤
local instance (p : Par) : MeasurableSingletonClass (Option (Mark p)) := ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (SourceState p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (SourceState p) := ⟨fun _ => trivial⟩
end
end CTMCHeredity20261019.CF3RawPathLift
namespace CTMCHeredity20261019
noncomputable section
open FunctionalCapacity
abbrev CappedSource (p : Par) := Fin p.M → Site p.c p.N
end
end CTMCHeredity20261019
namespace CTMCHeredity20261019
open FunctionalCapacity
open scoped BigOperators Classical
noncomputable section
variable {p : Par}
def sourceResetQ (x : CappedSource p) : CappedSource p :=
  fun i => { x i with q := fun _ => 0 }
def sourceResetAll (x : CappedSource p) : CappedSource p :=
  fun i => { x i with q := fun _ => 0, nd := 0 }
end
end CTMCHeredity20261019
namespace CTMCHeredity20261019
open MeasureTheory ProbabilityTheory Preorder Set
open scoped BigOperators ENNReal
noncomputable section
abbrev CutPrefix (S : Type*) (n : ℕ) := ∀ _ : Finset.Iic n, ℝ × S
def cutPrefixArrival {S : Type*} (n : ℕ) (u : CutPrefix S n) : ℝ :=
  ∑ i ∈ Finset.range n,
    if hi : i + 1 ≤ n then max 0 (u ⟨i + 1, Finset.mem_Iic.mpr hi⟩).1 else 0
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
end
end CTMCHeredity20261019
namespace CTMCHeredity20261019
noncomputable section
open FunctionalCapacity HybridCTMC.Kernel MeasureTheory
open scoped Classical ENNReal
theorem canonicalSeedFree_valid : canonicalSeedFreeCF3.Valid := by sorry
section PhysicalLaw
end PhysicalLaw
end
end CTMCHeredity20261019
namespace CTMCHeredity20261019.V2.Operated
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical
noncomputable section
abbrev History (X W : Type) (n : ℕ) := (Fin n → W) × X
def prepend {X W : Type} (n : ℕ) (z : W × History X W n) : History X W (n + 1) :=
  (Fin.cons z.1 z.2.1, z.2.2)
def tail {X W : Type} {n : ℕ} (h : History X W (n + 1)) : History X W n :=
  (fun i => h.1 i.succ, h.2)
section Construction
variable {X W : Type} [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
  [MeasurableSpace W]
def tailKernel {n : ℕ} (next : W → X) (hnext : Measurable next)
    (ν : X → Measure (History X W n)) : ProbabilityTheory.Kernel W (History X W n) where
  toFun w := ν (next w)
  measurable' := (measurable_of_countable ν).comp hnext
def law (κ : ProbabilityTheory.Kernel X W) (next : W → X) (hnext : Measurable next) :
    (n : ℕ) → X → Measure (History X W n)
  | 0, x => Measure.dirac ((fun i : Fin 0 => Fin.elim0 i), x)
  | n + 1, x =>
      ((κ x).compProd (tailKernel next hnext (law κ next hnext n))).map (prepend n)
end Construction
section Ambient
open HybridCTMC.Kernel
variable {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
end Ambient
end
end CTMCHeredity20261019.V2.Operated
namespace CTMCHeredity20261019.V2.RawOperated
open FunctionalCapacity MeasureTheory ProbabilityTheory Set HybridCTMC.Kernel
open CF3Marked CF3RawPathLift
open scoped BigOperators ENNReal Classical
noncomputable section
local instance (p : Par) : MeasurableSpace (SourceState p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (SourceState p) := ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (CF3MarkedKernel.State p) := ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (Option (Mark p)) := ⊤
local instance (p : Par) : MeasurableSingletonClass (Option (Mark p)) := ⟨fun _ => trivial⟩
abbrev RawPath (p : Par) := ℕ → ℝ × SourceState p
abbrev Segment (p : Par) := MarkedPath p × RawPath p
abbrev History (p : Par) (n : ℕ) := Operated.History (SourceState p) (Segment p) n
def rawPair (p : Par) (x : SourceState p) (w : MarkedPath p) : Segment p :=
  (w, rawSequence p x w)
def segmentKernel {p : Par} (hp : p.Valid) : ProbabilityTheory.Kernel (SourceState p) (Segment p) where
  toFun x := (CF3MarkedKernel.eventLaw hp (coreProject x) none).map (rawPair p x)
  measurable' := measurable_of_countable _
def nextState (p : Par) (T : ℝ) (s : Segment p) : SourceState p :=
  sourceResetQ (timedState T s.2)
theorem measurable_nextState (p : Par) (T : ℝ) : Measurable (nextState p T) := by sorry
theorem _root_.CTMCHeredity20261019.V2.RawOperated.rawLaw._proof_1 : ∀ {p : FunctionalCapacity.Par}, Countable (Fin p.M → FunctionalCapacity.Site p.c p.N) := by sorry
attribute [local instance] CTMCHeredity20261019.V2.RawOperated.rawLaw._proof_1
def rawLaw {p : Par} (hp : p.Valid) (T : ℝ) (n : ℕ) (x : SourceState p) :
    Measure (History p n) :=
  Operated.law (segmentKernel hp) (nextState p T) (measurable_nextState p T) n x
end
end CTMCHeredity20261019.V2.RawOperated
namespace CTMCHeredity20261019.V2.SeedSwitch
open FunctionalCapacity MeasureTheory ProbabilityTheory HybridCTMC.Kernel
open CF3Marked CF3RawPathLift
open scoped BigOperators ENNReal Classical
noncomputable section
attribute [local instance] CTMCHeredity20261019.V2.SeedSwitch.blockDuration._proof_1 CTMCHeredity20261019.V2.SeedSwitch.canonicalSeedOnCF3._proof_3 CTMCHeredity20261019.V2.SeedSwitch.canonicalSeedOnCF3._proof_2 CTMCHeredity20261019.V2.SeedSwitch.canonicalSeedOnCF3._proof_1
def canonicalSeedOnCF3 : Par := ⟨4, 3, 2048, 800, 4000000, 6⟩
abbrev seedOff : Par := canonicalSeedFreeCF3
abbrev Raw := SourceState seedOff
theorem seedOn_valid : canonicalSeedOnCF3.Valid := by sorry
local instance (p : Par) : MeasurableSpace (SourceState p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (SourceState p) := ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (CF3MarkedKernel.State p) :=
  ⟨fun _ => trivial⟩
def blockDuration : ℝ := 1 / 10
abbrev PhaseHistory := RawOperated.History seedOff 300
abbrev TwoPhaseHistory := PhaseHistory × PhaseHistory
def afterSwitchKernel : ProbabilityTheory.Kernel PhaseHistory PhaseHistory where
  toFun h := RawOperated.rawLaw canonicalSeedFree_valid blockDuration 300 (sourceResetAll h.2)
  measurable' := (measurable_of_countable
    (fun y : Raw => RawOperated.rawLaw canonicalSeedFree_valid blockDuration 300 y)).comp
      ((measurable_of_countable (sourceResetAll (p := seedOff))).comp measurable_snd)
def switchedLaw (x : Raw) : Measure TwoPhaseHistory :=
  (RawOperated.rawLaw seedOn_valid blockDuration 300 (sourceResetAll x)).compProd
    afterSwitchKernel
end
end CTMCHeredity20261019.V2.SeedSwitch
namespace P161Formal
open scoped BigOperators
noncomputable section
abbrev RecoveryMark := CTMCHeredity20261019.CF3Marked.Mark (literalSourcePar 0)
def isDivisionProposal : Option RecoveryMark → Bool
  | some (Sum.inr _) => true
  | some (Sum.inl _) | none => false
end
end P161Formal
namespace P161Formal
open CTMCHeredity20261019 CTMCHeredity20261019.CF3Marked
open scoped BigOperators Classical
noncomputable section
abbrev RecoveryMarkedState := CF3MarkedKernel.State (literalSourcePar 0)
abbrev recoveryStateDivision (z : RecoveryMarkedState) : Prop := isDivisionProposal z.2 = true
end
end P161Formal
namespace CTMCHeredity20261019.V2.PhysicalSplice
open MeasureTheory ProbabilityTheory Preorder Set HybridCTMC.Kernel
open scoped ENNReal Classical
noncomputable section
abbrev Path (S : Type*) := ℕ → ℝ × S
def prefixSplice {S : Type*} (n : ℕ) (T : ℝ)
    (z : CutPrefix S n × Path S) : Path S := fun k =>
  if hk : k ≤ n then z.1 ⟨k, Finset.mem_Iic.mpr hk⟩
  else if k = n + 1 then
    (T - cutPrefixArrival n z.1 + (z.2 1).1, (z.2 1).2)
  else z.2 (k - n)
def splice {S : Type*} (T : ℝ) (z : Path S × Path S) : Path S :=
  prefixSplice (clockIndex T z.1) T
    (frestrictLe (π := fun _ : ℕ => ℝ × S) (clockIndex T z.1) z.1, z.2)
section ActualLaw
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
variable [StandardBorelSpace S]
end ActualLaw
end
end CTMCHeredity20261019.V2.PhysicalSplice
namespace P161Formal
open MeasureTheory ProbabilityTheory Preorder HybridCTMC HybridCTMC.Kernel
open CTMCHeredity20261019
open scoped BigOperators ENNReal Classical
noncomputable section
local instance renewalStopsMeasurableSpace : MeasurableSpace RecoveryMarkedState := ⊤
local instance renewalStopsMeasurableSingleton : MeasurableSingletonClass RecoveryMarkedState :=
  ⟨fun _ => trivial⟩
abbrev RecoveryPath := ℕ → ℝ × RecoveryMarkedState
end
end P161Formal
namespace P161Formal
open MeasureTheory HybridCTMC HybridCTMC.Kernel CTMCHeredity20261019
open scoped Classical
noncomputable section
def physicalActualDivisionAt (w : RecoveryPath) (t : ℝ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ t = arrivalTime n w ∧ recoveryStateDivision (w n).2
end
end P161Formal
namespace CTMCHeredity20261019.V2.PhysicalOperated
open FunctionalCapacity MeasureTheory ProbabilityTheory Set HybridCTMC.Kernel
open CF3Marked CF3RawPathLift
open scoped ENNReal Classical
noncomputable section
local instance (p : Par) : MeasurableSpace (SourceState p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (SourceState p) := ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (CoreState p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (CoreState p) := ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (CF3MarkedKernel.State p) := ⟨fun _ => trivial⟩
def stitch (p : Par) (T : ℝ) : (n : ℕ) → RawOperated.History p n × MarkedPath p → MarkedPath p
  | 0, z => z.2
  | n + 1, z => PhysicalSplice.splice T
      ((z.1.1 0).1, stitch p T n (Operated.tail z.1, z.2))
end
end CTMCHeredity20261019.V2.PhysicalOperated
namespace CTMCHeredity20261019.V4.TwoPhaseIdentity
open FunctionalCapacity HybridCTMC.Kernel
open CTMCHeredity20261019.CF3Marked CTMCHeredity20261019.CF3RawPathLift
open CTMCHeredity20261019.V2
open SeedSwitch
open scoped BigOperators Classical
noncomputable section
abbrev Completion := TwoPhaseHistory × MarkedPath seedOff
def offPath (z : Completion) : MarkedPath seedOff :=
  PhysicalOperated.stitch seedOff blockDuration 300 (z.1.2, z.2)
def wholePath (z : Completion) : MarkedPath canonicalSeedOnCF3 :=
  PhysicalOperated.stitch canonicalSeedOnCF3 blockDuration 300 (z.1.1, offPath z)
end
end CTMCHeredity20261019.V4.TwoPhaseIdentity
namespace CTMCHeredity20261019.V4.TwoPhaseLaw
open FunctionalCapacity MeasureTheory ProbabilityTheory HybridCTMC.Kernel
open CF3Marked CF3RawPathLift V2 V2.SeedSwitch
open scoped ENNReal Classical
noncomputable section
local instance (p : Par) : MeasurableSpace (SourceState p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (SourceState p) := ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (CF3MarkedKernel.State p) :=
  ⟨fun _ => trivial⟩
abbrev Completion := SeedSwitch.TwoPhaseHistory × MarkedPath seedOff
def terminalKernel : ProbabilityTheory.Kernel SeedSwitch.TwoPhaseHistory (MarkedPath seedOff) where
  toFun h := CF3MarkedKernel.eventLaw canonicalSeedFree_valid (coreProject h.2.2) none
  measurable' := (measurable_of_countable (fun y : Raw =>
    CF3MarkedKernel.eventLaw canonicalSeedFree_valid (coreProject y) none)).comp
      (measurable_snd.comp measurable_snd)
def completedSwitchLaw (x : Raw) : Measure Completion :=
  (SeedSwitch.switchedLaw x).compProd terminalKernel
end
end CTMCHeredity20261019.V4.TwoPhaseLaw
set_option autoImplicit false
namespace P161Formal
open MeasureTheory HybridCTMC HybridCTMC.Kernel CTMCHeredity20261019
open CF3Marked CF3RawPathLift V2 V2.SeedSwitch V4.TwoPhaseIdentity
open scoped BigOperators Classical
noncomputable section
attribute [local instance] P161Formal.globalSourceDivisionAt._proof_1 P161Formal.sourceGlobalInitial._proof_1
local instance missionObsLiteralRawMeasurableSpace : MeasurableSpace (SourceState (literalSourcePar 0)) := ⊤
local instance missionObsLiteralRawMeasurableSingleton :
    MeasurableSingletonClass (SourceState (literalSourcePar 0)) := ⟨fun _ => trivial⟩
local instance missionObsLiteralMarkedMeasurableSpace :
    MeasurableSpace (CF3MarkedKernel.State (literalSourcePar 0)) := ⊤
local instance missionObsLiteralMarkedMeasurableSingleton :
    MeasurableSingletonClass (CF3MarkedKernel.State (literalSourcePar 0)) := ⟨fun _ => trivial⟩
def sourceGlobalInitial : (x : CTMCHeredity20261019.V2.SeedSwitch.Raw) → CTMCHeredity20261019.SourceState (P161Formal.literalSourcePar (@OfNat.ofNat.{0} Real (nat_lit 6) (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))) :=
  fun (x : CTMCHeredity20261019.V2.SeedSwitch.Raw) => @CTMCHeredity20261019.sourceResetAll (P161Formal.literalSourcePar (@OfNat.ofNat.{0} Real (nat_lit 6) (@instOfNatAtLeastTwo.{0}
  Real (nat_lit 6) Real.instNatCast P161Formal.sourceGlobalInitial._proof_1))) x
def sourceGlobalPrefix (z : V4.TwoPhaseLaw.Completion) (t : ℝ) : ℕ := clockIndex t (wholePath z)
def globalSourceDivisionAt (z : V4.TwoPhaseLaw.Completion) (t : ℝ) : Prop :=
  if t < 30 then physicalActualDivisionAt (wholePath z) t else physicalActualDivisionAt (offPath z) (t-30)
end
end P161Formal
namespace P161Formal
set_option bootstrap.genMatcherCode false
def unlimitedRun {S M : Type} (step : S → M → S) (initial : S) (marks : ℕ → M) : ℕ → S
  | 0 => initial
  | n + 1 => step (unlimitedRun step initial marks n) (marks n)
def stockStoppedRun {S M : Type} (allowed : S → Prop) [DecidablePred allowed]
    (step : S → M → S) (initial : S) (marks : ℕ → M) : ℕ → Option S
  | 0 => if allowed initial then some initial else none
  | n + 1 => match stockStoppedRun allowed step initial marks n with
    | none => none
    | some x => let y := step x (marks n); if allowed y then some y else none
set_option bootstrap.genMatcherCode true
end P161Formal
set_option autoImplicit false
namespace P161Formal
open HybridCTMC HybridCTMC.Kernel CTMCHeredity20261019
open CF3Marked CF3RawPathLift V2 V2.SeedSwitch V4.TwoPhaseIdentity
open scoped BigOperators Classical
noncomputable section
attribute [local instance] P161Formal.sourceStockStep._proof_1
@[ext] structure SourceStockState where
  raw : SourceState (literalSourcePar (@OfNat.ofNat ℝ (nat_lit 6) (@instOfNatAtLeastTwo ℝ (nat_lit 6) Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 5 (@Nat.instNeZeroSucc 4)))))
  feed : ℕ
  seeds : ℕ
  consumed : ℕ
  births : ℕ
  divisions : ℕ
  victimFuel : ℕ
def SourceStockState.allowed (s : SourceStockState) : Prop :=
  s.feed ≤ 800000000 ∧ s.seeds ≤ 5000 ∧ s.consumed+s.victimFuel ≤ 800000004 ∧
    s.births+s.seeds ≤ 800005004 ∧ s.divisions ≤ 1200 ∧
      3*2048*s.divisions ≤ 7372800 ∧ s.victimFuel ≤ 1200
def sourceStockInitial (x : Raw) : SourceStockState :=
  ⟨sourceGlobalInitial x,0,0,0,0,0,0⟩
def sourceStockStep : (s : P161Formal.SourceStockState) → (m : Option.{0} (CTMCHeredity20261019.CF3Marked.Mark (P161Formal.literalSourcePar (@OfNat.ofNat.{0} Real (nat_lit 6) (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))))) → P161Formal.SourceStockState :=
  fun (s : P161Formal.SourceStockState) (m : Option.{0} (CTMCHeredity20261019.CF3Marked.Mark (P161Formal.literalSourcePar (@OfNat.ofNat.{0} Real (nat_lit 6)
  (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast P161Formal.sourceStockStep._proof_1))))) => P161Formal.SourceStockState.mk
  (CTMCHeredity20261019.CF3RawPathLift.sourceProposalNext (P161Formal.literalSourcePar (@OfNat.ofNat.{0} Real (nat_lit 6) (@instOfNatAtLeastTwo.{0} Real (nat_lit 6)
  Real.instNatCast P161Formal.sourceStockStep._proof_1))) (P161Formal.SourceStockState.raw s) m) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
  (P161Formal.SourceStockState.feed s) (@P161Formal.sourceMarkFeed (@OfNat.ofNat.{0} Real (nat_lit 6) (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
  P161Formal.sourceStockStep._proof_1)) m)) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (P161Formal.SourceStockState.seeds s) (@P161Formal.sourceMarkSeeds
  (@OfNat.ofNat.{0} Real (nat_lit 6) (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast P161Formal.sourceStockStep._proof_1)) m)) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
  (@instHAdd.{0} Nat instAddNat) (P161Formal.SourceStockState.consumed s) (@P161Formal.sourceMarkConsumed (@OfNat.ofNat.{0} Real (nat_lit 6) (@instOfNatAtLeastTwo.{0} Real (nat_lit
  6) Real.instNatCast P161Formal.sourceStockStep._proof_1)) m)) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (P161Formal.SourceStockState.births s)
  (@P161Formal.sourceMarkBirths (@OfNat.ofNat.{0} Real (nat_lit 6) (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast P161Formal.sourceStockStep._proof_1)) m))
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (P161Formal.SourceStockState.divisions s) (@P161Formal.sourceMarkDivision (@OfNat.ofNat.{0} Real (nat_lit 6)
  (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast P161Formal.sourceStockStep._proof_1)) m)) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
  (P161Formal.SourceStockState.victimFuel s) (@P161Formal.sourceMarkVictimFuel (@OfNat.ofNat.{0} Real (nat_lit 6) (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
  P161Formal.sourceStockStep._proof_1)) (P161Formal.SourceStockState.raw s) m))
def sourceStockMarks (z : V4.TwoPhaseLaw.Completion) (k : ℕ) : Option (Mark (literalSourcePar (@OfNat.ofNat ℝ (nat_lit 6) (@instOfNatAtLeastTwo ℝ (nat_lit 6) Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 5 (@Nat.instNeZeroSucc 4)))))) :=
  (wholePath z (k+1)).2.2
def sourceStockRun : (x : CTMCHeredity20261019.V2.SeedSwitch.Raw) → (z : CTMCHeredity20261019.V4.TwoPhaseLaw.Completion) → Nat → Option.{0} P161Formal.SourceStockState :=
  fun (x : CTMCHeredity20261019.V2.SeedSwitch.Raw) (z : CTMCHeredity20261019.V4.TwoPhaseLaw.Completion) => @P161Formal.stockStoppedRun P161Formal.SourceStockState (Option.{0}
  (CTMCHeredity20261019.CF3Marked.Mark (P161Formal.literalSourcePar (@OfNat.ofNat.{0} Real (nat_lit 6) (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
  P161Formal.sourceStockStep._proof_1))))) P161Formal.SourceStockState.allowed (fun (a : P161Formal.SourceStockState) => Classical.propDecidable
  (P161Formal.SourceStockState.allowed a)) P161Formal.sourceStockStep (P161Formal.sourceStockInitial x) (P161Formal.sourceStockMarks z)
end
end P161Formal
set_option autoImplicit false
namespace P161Formal
open MeasureTheory ProbabilityTheory HybridCTMC HybridCTMC.Kernel CTMCHeredity20261019
open CF3Marked CF3RawPathLift V2 V2.SeedSwitch V4.TwoPhaseIdentity
open scoped Classical
noncomputable section
instance sourceOptionStockMeasurableSpace : MeasurableSpace (Option SourceStockState) := ⊤
local instance stockProcessGenericRawMeasurableSpace (p : FunctionalCapacity.Par) : MeasurableSpace (SourceState p) := ⊤
local instance stockProcessGenericRawMeasurableSingleton (p : FunctionalCapacity.Par) :
    MeasurableSingletonClass (SourceState p) := ⟨fun _ => trivial⟩
local instance stockProcessGenericMarkedMeasurableSpace (p : FunctionalCapacity.Par) :
    MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance stockProcessGenericMarkedMeasurableSingleton (p : FunctionalCapacity.Par) :
    MeasurableSingletonClass (CF3MarkedKernel.State p) := ⟨fun _ => trivial⟩
local instance stockProcessGenericOptionMeasurableSpace (p : FunctionalCapacity.Par) : MeasurableSpace (Option (Mark p)) := ⊤
local instance stockProcessGenericOptionMeasurableSingleton (p : FunctionalCapacity.Par) :
    MeasurableSingletonClass (Option (Mark p)) := ⟨fun _ => trivial⟩
local instance stockProcessRawMeasurableSpace : MeasurableSpace (SourceState (literalSourcePar 0)) := ⊤
local instance stockProcessRawMeasurableSingleton :
    MeasurableSingletonClass (SourceState (literalSourcePar 0)) := ⟨fun _ => trivial⟩
local instance stockProcessMarkedMeasurableSpace :
    MeasurableSpace (CF3MarkedKernel.State (literalSourcePar 0)) := ⊤
local instance stockProcessMarkedMeasurableSingleton :
    MeasurableSingletonClass (CF3MarkedKernel.State (literalSourcePar 0)) := ⟨fun _ => trivial⟩
local instance stockProcessOptionMeasurableSpace : MeasurableSpace (Option (Mark (literalSourcePar 0))) := ⊤
local instance stockProcessOptionMeasurableSingleton :
    MeasurableSingletonClass (Option (Mark (literalSourcePar 0))) := ⟨fun _ => trivial⟩
end
end P161Formal
set_option autoImplicit false
namespace P161Formal
open MeasureTheory HybridCTMC HybridCTMC.Kernel CTMCHeredity20261019
open CF3Marked CF3RawPathLift V2 V2.SeedSwitch V4.TwoPhaseIdentity
open scoped Classical
noncomputable section
attribute [local instance] P161Formal.emptyStockPopulation._proof_1
local instance stoppedObsGenericRawMeasurableSpace (p : FunctionalCapacity.Par) : MeasurableSpace (SourceState p) := ⊤
local instance stoppedObsGenericRawMeasurableSingleton (p : FunctionalCapacity.Par) :
    MeasurableSingletonClass (SourceState p) := ⟨fun _ => trivial⟩
local instance stoppedObsGenericMarkedMeasurableSpace (p : FunctionalCapacity.Par) :
    MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance stoppedObsGenericMarkedMeasurableSingleton (p : FunctionalCapacity.Par) :
    MeasurableSingletonClass (CF3MarkedKernel.State p) := ⟨fun _ => trivial⟩
local instance stoppedObsRawMeasurableSpace : MeasurableSpace (SourceState (literalSourcePar 0)) := ⊤
local instance stoppedObsRawMeasurableSingleton :
    MeasurableSingletonClass (SourceState (literalSourcePar 0)) := ⟨fun _ => trivial⟩
local instance stoppedObsMarkedMeasurableSpace :
    MeasurableSpace (CF3MarkedKernel.State (literalSourcePar 0)) := ⊤
local instance stoppedObsMarkedMeasurableSingleton :
    MeasurableSingletonClass (CF3MarkedKernel.State (literalSourcePar 0)) := ⟨fun _ => trivial⟩
def emptyStockPopulation : Population := ⟨fun _ _ => 0,fun _ => false⟩
end
end P161Formal
set_option autoImplicit false
namespace P161Formal
open MeasureTheory ProbabilityTheory HybridCTMC HybridCTMC.Kernel CTMCHeredity20261019
open CF3Marked CF3RawPathLift V2 V2.SeedSwitch V4.TwoPhaseIdentity
open scoped Classical ENNReal
noncomputable section
attribute [local instance] P161Formal.sourceRealizedObservations._proof_1
local instance finiteMissionGenericRawMeasurableSpace (p : FunctionalCapacity.Par) : MeasurableSpace (SourceState p) := ⊤
local instance finiteMissionGenericRawMeasurableSingleton (p : FunctionalCapacity.Par) :
    MeasurableSingletonClass (SourceState p) := ⟨fun _ => trivial⟩
local instance finiteMissionGenericMarkedMeasurableSpace (p : FunctionalCapacity.Par) :
    MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance finiteMissionGenericMarkedMeasurableSingleton (p : FunctionalCapacity.Par) :
    MeasurableSingletonClass (CF3MarkedKernel.State p) := ⟨fun _ => trivial⟩
local instance finiteMissionRawMeasurableSpace : MeasurableSpace (SourceState (literalSourcePar 0)) := ⊤
local instance finiteMissionRawMeasurableSingleton :
    MeasurableSingletonClass (SourceState (literalSourcePar 0)) := ⟨fun _ => trivial⟩
local instance finiteMissionMarkedMeasurableSpace :
    MeasurableSpace (CF3MarkedKernel.State (literalSourcePar 0)) := ⊤
local instance finiteMissionMarkedMeasurableSingleton :
    MeasurableSingletonClass (CF3MarkedKernel.State (literalSourcePar 0)) := ⟨fun _ => trivial⟩
abbrev SourceStockPath := ℕ → Option SourceStockState
abbrev SourceRealizedStockTrace := V4.TwoPhaseLaw.Completion × SourceStockPath
def sourceRealizedStockTrace (x : Raw) (z : V4.TwoPhaseLaw.Completion) : SourceRealizedStockTrace :=
  (z,sourceStockRun x z)
def sourceRealizedFiniteStockLaw (x : Raw) : Measure SourceRealizedStockTrace :=
  (V4.TwoPhaseLaw.completedSwitchLaw x).map (sourceRealizedStockTrace x)
def sourceRealizedObservations (u : SourceRealizedStockTrace) : MissionObservations where
  state t := ((u.2 (sourceGlobalPrefix u.1 t)).map (fun s => sourcePopulation (seed := 6) s.raw)).getD emptyStockPopulation
  credits t i j := ((u.2 (sourceGlobalPrefix u.1 t)).map (fun s => @FunctionalCapacity.Site.q (FunctionalCapacity.Par.c (literalSourcePar 6)) (FunctionalCapacity.Par.N (literalSourcePar 6)) (s.raw i) j)).getD 0
  initiatingDivisions t i := ((u.2 (sourceGlobalPrefix u.1 t)).map (fun s => @FunctionalCapacity.Site.nd (FunctionalCapacity.Par.c (literalSourcePar 6)) (FunctionalCapacity.Par.N (literalSourcePar 6)) (s.raw i))).getD 0
  feed t := ((u.2 (sourceGlobalPrefix u.1 t)).map SourceStockState.feed).getD 0
  seeds t := ((u.2 (sourceGlobalPrefix u.1 t)).map SourceStockState.seeds).getD 0
  consumedFuel t := ((u.2 (sourceGlobalPrefix u.1 t)).map (fun s => s.consumed+s.victimFuel)).getD 0
  precursors t := ((u.2 (sourceGlobalPrefix u.1 t)).map (fun s => s.births+s.seeds)).getD 0
  divisions t := ((u.2 (sourceGlobalPrefix u.1 t)).map SourceStockState.divisions).getD 0
  victimSlots t := ((u.2 (sourceGlobalPrefix u.1 t)).map (fun s => 3*2048*s.divisions)).getD 0
  victimFuel t := ((u.2 (sourceGlobalPrefix u.1 t)).map SourceStockState.victimFuel).getD 0
  isDivision t := globalSourceDivisionAt u.1 t ∧ u.2 (sourceGlobalPrefix u.1 t) ≠ none
theorem template_free_heredity_finite_stock (x : Raw)
    (hx : ∀ i : SiteId, 512 ≤ ((x i).a (0 : SpeciesId)).val ∧
      512 ≤ ((x i).a (1 : SpeciesId)).val) :
    sourceRealizedFiniteStockLaw x {u | ¬completeMission (sourceRealizedObservations u)} ≤
      ENNReal.ofReal failureCeiling := by sorry
end
end P161Formal

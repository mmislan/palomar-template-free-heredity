module

public import proofs.CTMCHeredity20261019.SourceKilled
public import proofs.CTMCHeredity20261019.CF3Capped
public import proofs.CTMCHeredity20261019.QuotientTransfer

@[expose] public section

/-!
# Exact docking of the CF3 grid mission on its finite saturation carrier

The source predicates, reset operations, terminal division indicator, and
two-phase mission below are the literal formulas from FunctionalCapacity.Mission.
Their names are private so importing the heavyweight mission proof is unnecessary.
The equalities preserve the complete killed tick, its Poisson mixture, every
grid service check, both ledger resets, and the final division threshold.

These are scalar operator identities. Identification with a physical joint
multi-horizon path event is a separate obligation.
-/

namespace CTMCHeredity20261019

open FunctionalCapacity
open scoped BigOperators Classical
noncomputable section

variable {p : Par}

/-- The source's floor-violation predicate, with every required site/species. -/
def sourceDead (K : ℕ) (req : Finset (Fin p.c)) (x : CappedSource p) : Prop :=
  ∃ i, ∃ j ∈ req, ((x i).a j : ℕ) < K

/-- The source's block service requirement at every required site/species. -/
def sourceOkS (m : ℕ) (req : Finset (Fin p.c)) (x : CappedSource p) : Prop :=
  ∀ i, ∀ j ∈ req, m ≤ (x i).q j

/-- The source's terminal requirement that every site divided at least d times. -/
def sourceFinalD (d : ℕ) (x : CappedSource p) : ℝ :=
  if ∀ i, d ≤ (x i).nd then 1 else 0

/-- Reset only the output ledgers at an ordinary block boundary. -/
def sourceResetQ (x : CappedSource p) : CappedSource p :=
  fun i => { x i with q := fun _ => 0 }

/-- Reset outputs and divisions at the initial and phase boundaries. -/
def sourceResetAll (x : CappedSource p) : CappedSource p :=
  fun i => { x i with q := fun _ => 0, nd := 0 }

theorem sourceDead_eq_capped (Q D K : ℕ) (req : Finset (Fin p.c)) :
    sourceDead K req = fun x : CappedSource p =>
      cappedDead K req (capProject Q D x) := by
  funext x
  exact propext (cap_dead_iff Q D K req x)

theorem sourceOkS_eq_capped {Q D m : ℕ} (hm : m ≤ Q)
    (req : Finset (Fin p.c)) :
    sourceOkS m req = fun x : CappedSource p =>
      cappedOkS m req (capProject Q D x) := by
  funext x
  exact propext (cap_okS_iff hm req x)

theorem sourceFinalD_eq_capped {Q D d : ℕ} (hd : d ≤ D) :
    sourceFinalD d = fun x : CappedSource p => cappedFinalD d (capProject Q D x) := by
  funext x
  exact cap_finalD_eq hd x

theorem sourceResetQ_project (Q D : ℕ) (x : CappedSource p) :
    capProject Q D (sourceResetQ x) = cappedResetQ (capProject Q D x) :=
  cap_resetQ Q D x

theorem sourceResetAll_project (Q D : ℕ) (x : CappedSource p) :
    capProject Q D (sourceResetAll x) = cappedResetAll (capProject Q D x) :=
  cap_resetAll Q D x

/-- Literal CF3 source killed at an explicitly specified source predicate. -/
def cf3SourceKilled (hp : p.Valid) {Lam : ℝ} (hLam : 0 < Lam)
    (hRate : cf3Rate p ≤ Lam) (dead : CappedSource p → Prop) :
    SubMarkov (CappedSource p) :=
  generatorKilled (cf3_isGen hp) hLam hRate dead

/-- The same killed tick on the exact finite CF3 saturation quotient. -/
def cf3CappedKilled (hp : p.Valid) (Q D : ℕ) {Lam : ℝ} (hLam : 0 < Lam)
    (hRate : cf3Rate p ≤ Lam) (dead : CappedState p Q D → Prop) :
    SubMarkov (CappedState p Q D) :=
  generatorKilled (cappedGen_isGen hp Q D) hLam hRate dead

/-- Exact equality of the actual source/capped killed Poisson operators. -/
theorem cf3_capped_ct (hp : p.Valid) (Q D : ℕ) {Lam : ℝ}
    (hLam : 0 < Lam) (hRate : cf3Rate p ≤ Lam)
    (dead : CappedState p Q D → Prop) (μ : ℝ)
    (f : CappedState p Q D → ℝ) (x : CappedSource p) :
    (cf3SourceKilled hp hLam hRate (fun y => dead (capProject Q D y))).ct μ
      (fun y => f (capProject Q D y)) x =
      (cf3CappedKilled hp Q D hLam hRate dead).ct μ f (capProject Q D x) := by
  apply ct_quotient (capProject Q D)
  intro g y
  exact cf3_capped_stepK p Q D Lam dead g y

/-- Floor killing in the preceding equality is the source's raw floor formula. -/
theorem cf3_capped_floor_ct (hp : p.Valid) (Q D K : ℕ)
    (req : Finset (Fin p.c)) {Lam : ℝ} (hLam : 0 < Lam)
    (hRate : cf3Rate p ≤ Lam) (μ : ℝ) (f : CappedState p Q D → ℝ)
    (x : CappedSource p) :
    (cf3SourceKilled hp hLam hRate (sourceDead K req)).ct μ
      (fun y => f (capProject Q D y)) x =
      (cf3CappedKilled hp Q D hLam hRate (cappedDead K req)).ct μ f
        (capProject Q D x) := by
  rw [sourceDead_eq_capped Q D K req]
  exact cf3_capped_ct hp Q D hLam hRate (cappedDead K req) μ f x

/-- Every source block service test and output reset is preserved exactly. -/
theorem cf3_capped_blocks (hp : p.Valid) (Q D K m : ℕ) (hm : m ≤ Q)
    (req : Finset (Fin p.c)) {Lam : ℝ} (hLam : 0 < Lam)
    (hRate : cf3Rate p ≤ Lam) (μ : ℝ) (n : ℕ)
    (f : CappedState p Q D → ℝ) (x : CappedSource p) :
    blocks (cf3SourceKilled hp hLam hRate (sourceDead K req)) μ
      (sourceOkS m req) sourceResetQ n (fun y => f (capProject Q D y)) x =
      blocks (cf3CappedKilled hp Q D hLam hRate (cappedDead K req)) μ
        (cappedOkS m req) cappedResetQ n f (capProject Q D x) := by
  rw [sourceOkS_eq_capped (D := D) hm req]
  apply blocks_quotient (capProject Q D)
  · intro g y
    change stepK (cf3Gen p) Lam (sourceDead K req)
      (fun z => g (capProject Q D z)) y = _
    rw [sourceDead_eq_capped Q D K req]
    exact cf3_capped_stepK p Q D Lam (cappedDead K req) g y
  · exact sourceResetQ_project Q D

/-- The concrete CF3 grid operator, including its every-site division indicator,
has an exact finite-carrier representation whenever both thresholds fit the caps. -/
theorem cf3_capped_grid_blocks (hp : p.Valid) (Q D K m d : ℕ)
    (hm : m ≤ Q) (hd : d ≤ D) (req : Finset (Fin p.c)) {Lam : ℝ}
    (hLam : 0 < Lam) (hRate : cf3Rate p ≤ Lam) (μ : ℝ) (n : ℕ)
    (x : CappedSource p) :
    blocks (cf3SourceKilled hp hLam hRate (sourceDead K req)) μ
      (sourceOkS m req) sourceResetQ n (sourceFinalD d) x =
      blocks (cf3CappedKilled hp Q D hLam hRate (cappedDead K req)) μ
        (cappedOkS m req) cappedResetQ n (cappedFinalD d) (capProject Q D x) := by
  rw [sourceFinalD_eq_capped (Q := Q) hd]
  exact cf3_capped_blocks hp Q D K m hm req hLam hRate μ n (cappedFinalD d) x

/-- Positivity of the literal source clock rate, with the existing source proof. -/
theorem cf3_mission_rate_pos (hp : p.Valid) : 0 < cf3Rate p := by
  unfold cf3Rate
  have hM : (0 : ℝ) < p.M := by have := hp.hM; positivity
  have hc : (0 : ℝ) ≤ p.c := Nat.cast_nonneg _
  have hN : (0 : ℝ) ≤ p.N := Nat.cast_nonneg _
  have h1 : 0 ≤ (p.c : ℝ) * (p.ε + p.α * p.N + p.α / 2 * p.N + p.N + p.β) := by
    apply mul_nonneg hc
    have := hp.hα; have := hp.hβ; have := hp.hε
    have := mul_nonneg hp.hα hN
    nlinarith
  have := hp.hβ
  apply mul_pos hM
  linarith

/-- Raw source post-phase: all species required; output reset after every block;
division count checked at the terminal time. -/
def sourcePostValue (hp : p.Valid) (K m d Lp : ℕ) (w : ℝ) : CappedSource p → ℝ :=
  blocks (cf3SourceKilled hp (cf3_mission_rate_pos hp) le_rfl
    (sourceDead K Finset.univ)) (cf3Rate p * w)
    (sourceOkS m Finset.univ) sourceResetQ Lp (sourceFinalD d)

def cappedPostValue (hp : p.Valid) (Q D K m d Lp : ℕ) (w : ℝ) :
    CappedState p Q D → ℝ :=
  blocks (cf3CappedKilled hp Q D (cf3_mission_rate_pos hp) le_rfl
    (cappedDead K Finset.univ)) (cf3Rate p * w)
    (cappedOkS m Finset.univ) cappedResetQ Lp (cappedFinalD d)

theorem cf3_capped_postValue (hp : p.Valid) (Q D K m d Lp : ℕ)
    (hm : m ≤ Q) (hd : d ≤ D) (w : ℝ) (x : CappedSource p) :
    sourcePostValue hp K m d Lp w x =
      cappedPostValue hp Q D K m d Lp w (capProject Q D x) := by
  exact cf3_capped_grid_blocks hp Q D K m d hm hd Finset.univ
    (cf3_mission_rate_pos hp) le_rfl (cf3Rate p * w) Lp x

/-- Literal two-phase source mission: before acquisition, erase the candidate
from the required species; afterwards require every species. Reset both ledgers
initially and at acquisition, and reset only output ledgers between blocks. -/
def sourceMission (hp : p.Valid) (K m d La Lp : ℕ) (w : ℝ)
    (jc : Fin p.c) (x : CappedSource p) : ℝ :=
  blocks (cf3SourceKilled hp (cf3_mission_rate_pos hp) le_rfl
    (sourceDead K (Finset.univ.erase jc))) (cf3Rate p * w)
    (sourceOkS m (Finset.univ.erase jc)) sourceResetQ La
    (fun y => sourcePostValue hp K m d Lp w (sourceResetAll y)) (sourceResetAll x)

def cappedMission (hp : p.Valid) (Q D K m d La Lp : ℕ) (w : ℝ)
    (jc : Fin p.c) (x : CappedState p Q D) : ℝ :=
  blocks (cf3CappedKilled hp Q D (cf3_mission_rate_pos hp) le_rfl
    (cappedDead K (Finset.univ.erase jc))) (cf3Rate p * w)
    (cappedOkS m (Finset.univ.erase jc)) cappedResetQ La
    (fun y => cappedPostValue hp Q D K m d Lp w (cappedResetAll y)) (cappedResetAll x)

/-- The full two-phase source mission operator is exactly its finite saturation
quotient. No source rate, victim overwrite, floor check or ledger test is altered. -/
theorem cf3_capped_mission (hp : p.Valid) (Q D K m d La Lp : ℕ)
    (hm : m ≤ Q) (hd : d ≤ D) (w : ℝ) (jc : Fin p.c) (x : CappedSource p) :
    sourceMission hp K m d La Lp w jc x =
      cappedMission hp Q D K m d La Lp w jc (capProject Q D x) := by
  have ht : (fun y : CappedSource p =>
      sourcePostValue hp K m d Lp w (sourceResetAll y)) =
      (fun y : CappedSource p =>
        cappedPostValue hp Q D K m d Lp w (cappedResetAll (capProject Q D y))) := by
    funext y
    rw [cf3_capped_postValue hp Q D K m d Lp hm hd w,
      sourceResetAll_project Q D]
  unfold sourceMission cappedMission
  rw [ht]
  rw [cf3_capped_blocks hp Q D K m hm (Finset.univ.erase jc)
    (cf3_mission_rate_pos hp) le_rfl (cf3Rate p * w) La
    (fun y => cappedPostValue hp Q D K m d Lp w (cappedResetAll y))]
  rw [sourceResetAll_project Q D]

end
end CTMCHeredity20261019

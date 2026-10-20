module

public import proofs.CTMCHeredity20261019.MarkedUniformization
public import proofs.CTMCHeredity20261019.CF3Core

@[expose] public section

/-!
# The literal CF3 complete physical operation marks

Actual chemistry labels and actual division labels are distinguished. A division
label contains its initiating site, basal/trigger channel, one shared species/fuel
split, and victim. The full source update retains arbitrary external ledgers and
keeps the victim's external ledgers. An actual operation with a null projected
state update is still an actual `some` label; only `none` is a dummy proposal.

This constructs the one-proposal law and proves source generator identities.
It does not yet construct the timed marked process, random operation stops, or
gross-counter martingales needed by the full finite-stock mission.
-/

namespace CTMCHeredity20261019.CF3Marked

open FunctionalCapacity
open scoped BigOperators Classical
noncomputable section

/-- Chemistry, or a complete initiating-site/channel/split/victim division mark. -/
abbrev Mark (p : Par) :=
  (Fin p.M × Chem p.c) ⊕
    (Fin p.M × (Option (Fin p.c) × (Split p.c p.N × Fin p.M)))

def victimWeight (p : Par) (i v : Fin p.M) : ℝ :=
  if v = i then 0 else 1 / ((p.M : ℝ) - 1)

theorem victimWeight_nonneg {p : Par} (hp : p.Valid) (i v : Fin p.M) :
    0 ≤ victimWeight p i v := by
  unfold victimWeight
  split_ifs
  · exact le_refl 0
  · exact div_nonneg (by norm_num) (cast_sub_one_pos hp.hM).le

theorem victimWeight_sum {p : Par} (hp : p.Valid) (i : Fin p.M) :
    ∑ v, victimWeight p i v = 1 := by
  simpa only [victimWeight, mul_one] using sum_victim_const hp.hM i (1 : ℝ)

/-- Actual joint split and uniform distinct-victim probability. The two daughters
will use this same split mark, rather than independent sister samples. -/
def outcomeWeight {p : Par} (i : Fin p.M) (s : Site p.c p.N)
    (z : Split p.c p.N × Fin p.M) : ℝ :=
  (cf3 p).ps s z.1 * victimWeight p i z.2

theorem outcomeWeight_nonneg {p : Par} (hp : p.Valid) (i : Fin p.M)
    (s : Site p.c p.N) (z : Split p.c p.N × Fin p.M) :
    0 ≤ outcomeWeight i s z :=
  mul_nonneg (cf3_ps_nonneg s z.1) (victimWeight_nonneg hp i z.2)

theorem outcomeWeight_split_marginal {p : Par} (hp : p.Valid)
    (i : Fin p.M) (s : Site p.c p.N) (o : Split p.c p.N) :
    ∑ v, outcomeWeight i s (o, v) = (cf3 p).ps s o := by
  simp only [outcomeWeight, ← Finset.mul_sum, victimWeight_sum hp, mul_one]

theorem outcomeWeight_sum {p : Par} (hp : p.Valid)
    (i : Fin p.M) (s : Site p.c p.N) :
    ∑ z, outcomeWeight i s z = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [outcomeWeight_split_marginal hp]
  exact cf3_ps_sum s

theorem outcomeWeight_sum_iterated {p : Par} (hp : p.Valid)
    (i : Fin p.M) (s : Site p.c p.N) :
    (∑ o, ∑ v, outcomeWeight i s (o, v)) = 1 := by
  simpa only [Fintype.sum_prod_type] using outcomeWeight_sum hp i s

/-- A complete actual division on the original unbounded-ledger source state. -/
def divisionNext (p : Par) (x : SourceState p) (i : Fin p.M)
    (k : Option (Fin p.c)) (o : Split p.c p.N) (v : Fin p.M) : SourceState p :=
  Function.update
    (Function.update x i ((cf3 p).d1 ((cf3 p).td (x i) k) o)) v
    ((cf3 p).merge (x v) ((cf3 p).d2 ((cf3 p).td (x i) k) o))

/-- Deterministic complete source update for each retained physical mark. -/
def sourceNext (p : Par) (x : SourceState p) : Mark p → SourceState p
  | Sum.inl (i, k) => Function.update x i ((cf3 p).tc (x i) k)
  | Sum.inr (i, (k, (o, v))) => divisionNext p x i k o v

/-- Literal CF3 channel intensity, refined by the actual split/victim law. -/
def sourceIntensity (p : Par) (x : SourceState p) : Mark p → ℝ
  | Sum.inl (i, k) => (cf3 p).rc (x i) k
  | Sum.inr (i, (k, z)) => (cf3 p).rd (x i) k * outcomeWeight i ((cf3 p).td (x i) k) z

theorem sourceIntensity_nonneg {p : Par} (hp : p.Valid)
    (x : SourceState p) (r : Mark p) : 0 ≤ sourceIntensity p x r := by
  cases r with
  | inl a => exact cf3_rc_nonneg hp (x a.1) a.2
  | inr a =>
      exact mul_nonneg (cf3_rd_nonneg (x a.1) a.2.1)
        (outcomeWeight_nonneg hp a.1 _ a.2.2)

/-- This existing minimal source interface does not require a finite state type.
The retained mark type is finite even with arbitrary natural-valued ledgers. -/
def sourceChannels {p : Par} (hp : p.Valid) :
    HybridCTMC.Channels (SourceState p) (Mark p) where
  next := sourceNext p
  propensity := sourceIntensity p
  nonneg := sourceIntensity_nonneg hp

/-- Integrating the split/victim refinement recovers the actual division intensity. -/
theorem divisionIntensity_sum {p : Par} (hp : p.Valid) (x : SourceState p)
    (i : Fin p.M) (k : Option (Fin p.c)) :
    (∑ z, sourceIntensity p x (Sum.inr (i, (k, z)))) = (cf3 p).rd (x i) k := by
  simp only [sourceIntensity, ← Finset.mul_sum, outcomeWeight_sum hp, mul_one]

/-- The split marginal of an actual division is precisely the supplied source
`ps`, with the source's trigger-fuel update performed before the split. -/
theorem divisionSplitIntensity_sum {p : Par} (hp : p.Valid) (x : SourceState p)
    (i : Fin p.M) (k : Option (Fin p.c)) (o : Split p.c p.N) :
    (∑ v, sourceIntensity p x (Sum.inr (i, (k, (o, v))))) =
      (cf3 p).rd (x i) k * (cf3 p).ps ((cf3 p).td (x i) k) o := by
  simp only [sourceIntensity, ← Finset.mul_sum, outcomeWeight_split_marginal hp]

theorem sourceIntensity_sum {p : Par} (hp : p.Valid) (x : SourceState p) :
    (∑ r, sourceIntensity p x r) =
      ∑ i, ((∑ k, (cf3 p).rc (x i) k) + ∑ k, (cf3 p).rd (x i) k) := by
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, sourceIntensity,
    ← Finset.mul_sum, outcomeWeight_sum_iterated hp, mul_one]
  exact Finset.sum_add_distrib.symm

/-- The original source envelope pays the full marked rate, including actual
operations with a null projected state update. No labels are removed. -/
theorem sourceIntensity_bound {p : Par} (hp : p.Valid) (x : SourceState p) :
    ∑ r, sourceIntensity p x r ≤ cf3Rate p := by
  rw [sourceIntensity_sum hp]
  calc
    _ ≤ ∑ _i : Fin p.M,
        ((p.c * (p.ε + p.α * p.N + p.α / 2 * p.N + p.N + p.β) + p.β) +
          (1 + p.c)) := Finset.sum_le_sum fun i _ =>
      add_le_add (cf3_rc_sum_le hp (x i)) (cf3_rd_sum_le (x i))
    _ = cf3Rate p := by
      simp [cf3Rate]
      ring

/-- Exact full-source generator identity. This theorem retains q/nd and every
victim-ledger update, and requires no finite-source-state fiction. -/
theorem source_generator {p : Par} (f : SourceState p → ℝ) (x : SourceState p) :
    (∑ r, sourceIntensity p x r * (f (sourceNext p x r) - f x)) = cf3Gen p f x := by
  unfold cf3Gen popGen
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, sourceIntensity,
    sourceNext, Finset.sum_add_distrib, Finset.mul_sum]
  refine congrArg₂ (fun a b : ℝ => a + b) rfl ?_
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro o _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro victim _
  unfold outcomeWeight victimWeight divisionNext
  split_ifs <;> ring

/-- The actual normalized one-proposal mark law on the complete source. -/
def sourceLaw {p : Par} (hp : p.Valid) {Lam : ℝ} (hLam : 0 < Lam)
    (hbound : cf3Rate p ≤ Lam) (x : SourceState p) : PMF (Option (Mark p)) :=
  MarkedUniformization.law (sourceChannels hp) hLam
    (fun y => (sourceIntensity_bound hp y).trans hbound) x

theorem sourceLaw_real {p : Par} (hp : p.Valid) {Lam : ℝ} (hLam : 0 < Lam)
    (hbound : cf3Rate p ≤ Lam) (x : SourceState p) (r : Mark p) :
    (sourceLaw hp hLam hbound x (some r)).toReal = sourceIntensity p x r / Lam := by
  simp only [sourceLaw, MarkedUniformization.law_apply_real,
    MarkedUniformization.weight, sourceChannels]

/-- The exact expected full-state update under the labelled proposal law. -/
theorem source_expect_next {p : Par} (hp : p.Valid) (Lam : ℝ)
    (f : SourceState p → ℝ) (x : SourceState p) :
    MarkedUniformization.expect (sourceChannels hp) Lam x
      (fun m => f (MarkedUniformization.next (sourceChannels hp) x m)) =
      f x + cf3Gen p f x / Lam := by
  rw [MarkedUniformization.expect_next_sum]
  change f x + (∑ r, sourceIntensity p x r * (f (sourceNext p x r) - f x)) / Lam = _
  rw [source_generator]

theorem sourceLaw_division_mass {p : Par} (hp : p.Valid) {Lam : ℝ}
    (hLam : 0 < Lam) (hbound : cf3Rate p ≤ Lam) (x : SourceState p)
    (i : Fin p.M) (k : Option (Fin p.c)) :
    (∑ z, (sourceLaw hp hLam hbound x (some (Sum.inr (i, (k, z))))).toReal) =
      (cf3 p).rd (x i) k / Lam := by
  simp only [sourceLaw_real]
  rw [← Finset.sum_div, divisionIntensity_sum hp]

theorem sourceLaw_division_split_mass {p : Par} (hp : p.Valid) {Lam : ℝ}
    (hLam : 0 < Lam) (hbound : cf3Rate p ≤ Lam) (x : SourceState p)
    (i : Fin p.M) (k : Option (Fin p.c)) (o : Split p.c p.N) :
    (∑ v, (sourceLaw hp hLam hbound x (some (Sum.inr (i, (k, (o, v)))))).toReal) =
      ((cf3 p).rd (x i) k * (cf3 p).ps ((cf3 p).td (x i) k) o) / Lam := by
  simp only [sourceLaw_real]
  rw [← Finset.sum_div, divisionSplitIntensity_sum hp]

/-- Normalizing the selected positive-rate division channel gives its actual
source split distribution. The numerator sums the distinct victim marks; the
denominator sums all distinct split/victim marks of that same channel. -/
theorem conditional_division_split {p : Par} (hp : p.Valid) {Lam : ℝ}
    (hLam : 0 < Lam) (hbound : cf3Rate p ≤ Lam) (x : SourceState p)
    (i : Fin p.M) (k : Option (Fin p.c)) (hrd : 0 < (cf3 p).rd (x i) k)
    (o : Split p.c p.N) :
    (∑ v, (sourceLaw hp hLam hbound x (some (Sum.inr (i, (k, (o, v)))))).toReal) /
      (∑ z, (sourceLaw hp hLam hbound x (some (Sum.inr (i, (k, z))))).toReal) =
      (cf3 p).ps ((cf3 p).td (x i) k) o := by
  rw [sourceLaw_division_split_mass, sourceLaw_division_mass]
  field_simp [hLam.ne', hrd.ne']

/-- Only after quotienting the actual source update do we use a finite-state
channel kernel. The preceding raw-source generator identity remains primary. -/
def coreChannels {p : Par} (hp : p.Valid) :
    HybridCTMC.Channels (CoreState p) (Mark p) where
  next x r := coreProject (sourceNext p (coreRepresent x) r)
  propensity x r := sourceIntensity p (coreRepresent x) r
  nonneg x r := sourceIntensity_nonneg hp (coreRepresent x) r

theorem coreChannels_generator {p : Par} (hp : p.Valid)
    (f : CoreState p → ℝ) (x : CoreState p) :
    (coreChannels hp).rates.generator f x = coreGen p f x := by
  rw [HybridCTMC.Channels.generator_eq]
  have h := source_generator (p := p) (fun y => f (coreProject y)) (coreRepresent x)
  simpa only [coreChannels, coreGen, coreProject_represent] using h

/-- The core-labelled update erases to the independently constructed finite
uniformization on every observable. This is a one-step identity, not a timed
path or unbounded-ledger erasure theorem. -/
theorem core_expect_eq_uniformizedKernel {p : Par} (hp : p.Valid) {Lam : ℝ}
    (hLam : 0 < Lam) (hbound : cf3Rate p ≤ Lam)
    (f : CoreState p → ℝ) (x : CoreState p) :
    MarkedUniformization.expect (coreChannels hp) Lam x
      (fun m => f (MarkedUniformization.next (coreChannels hp) x m)) =
      (uniformizedKernel (coreGen_isGen hp) hLam hbound).expect f x := by
  rw [MarkedUniformization.expect_next, coreChannels_generator,
    uniformizedKernel_expect]

end
end CTMCHeredity20261019.CF3Marked

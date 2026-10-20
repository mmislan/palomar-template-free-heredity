module

public import proofs.FunctionalCapacity.SiteCF3

@[expose] public section

/-!
# Exact finite saturation quotient of CF3, including the mission ledgers

Service and division counters are saturated at Q and D. All count/fuel
coordinates, source rates, chemical channels, and complementary simultaneous
two-daughter/victim transitions are retained. This finite quotient preserves
all ledger threshold tests up to the selected caps and commutes with the
source's reset-to-zero operations.

This is a source generator quotient. It does not itself construct the joint
block path law or identify an algebraic Poisson operator with a path event.
-/

namespace CTMCHeredity20261019

noncomputable section
open FunctionalCapacity

/-- Saturate a natural counter at B, retaining a finite carrier. -/
def capNat (B n : ℕ) : Fin (B + 1) := ⟨min n B, by omega⟩

@[simp] theorem capNat_val (B : ℕ) (n : Fin (B + 1)) : capNat B n.val = n := by
  apply Fin.ext
  exact Nat.min_eq_left (by omega)

@[simp] theorem capNat_zero (B : ℕ) : capNat B 0 = 0 := by
  apply Fin.ext
  simp [capNat]

/-- Increment and saturation commute, including a counter already at its cap. -/
@[simp] theorem capNat_recap_succ (B n : ℕ) :
    capNat B ((capNat B n).val + 1) = capNat B (n + 1) := by
  apply Fin.ext
  change min (min n B + 1) B = min (n + 1) B
  omega

theorem capNat_threshold {B m : ℕ} (hm : m ≤ B) (n : ℕ) :
    m ≤ (capNat B n : ℕ) ↔ m ≤ n := by
  change m ≤ min n B ↔ m ≤ n
  omega

/-- Saturating a counter-valued function commutes with one coordinate update. -/
theorem capMap_update {ι : Type} [DecidableEq ι] (B : ℕ) (q : ι → ℕ)
    (i : ι) (n : ℕ) :
    (fun j => capNat B (Function.update q i n j)) =
      Function.update (fun j => capNat B (q j)) i (capNat B n) := by
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [h]

/-- A finite compartment carrying the actual output and division counters,
with saturation rather than modulo arithmetic. -/
@[ext] structure CappedSite (c N Q D : ℕ) where
  a : Fin c → Fin (N + 1)
  R : Bool
  q : Fin c → Fin (Q + 1)
  nd : Fin (D + 1)
  deriving Fintype, DecidableEq

abbrev CappedState (p : Par) (Q D : ℕ) := Fin p.M → CappedSite p.c p.N Q D

abbrev CappedSource (p : Par) := Fin p.M → Site p.c p.N

def capSite {c N : ℕ} (Q D : ℕ) (s : Site c N) : CappedSite c N Q D where
  a := s.a
  R := s.R
  q := fun j => capNat Q (s.q j)
  nd := capNat D s.nd

/-- Choose the finite counter values themselves as the source representative. -/
def capRepresentSite {c N Q D : ℕ} (s : CappedSite c N Q D) : Site c N where
  a := s.a
  R := s.R
  q := fun j => (s.q j : ℕ)
  nd := s.nd

def capProject {p : Par} (Q D : ℕ) (x : CappedSource p) : CappedState p Q D :=
  fun i => capSite Q D (x i)

def capRepresent {p : Par} {Q D : ℕ} (x : CappedState p Q D) : CappedSource p :=
  fun i => capRepresentSite (x i)

@[simp] theorem capSite_represent {c N Q D : ℕ} (s : CappedSite c N Q D) :
    capSite Q D (capRepresentSite s) = s := by
  cases s
  simp [capSite, capRepresentSite]

@[simp] theorem capProject_represent {p : Par} {Q D : ℕ} (x : CappedState p Q D) :
    capProject Q D (capRepresent x) = x := by
  funext i
  exact capSite_represent (x i)

theorem capProject_surjective (p : Par) (Q D : ℕ) :
    Function.Surjective (capProject (p := p) Q D) := by
  intro x
  exact ⟨capRepresent x, capProject_represent x⟩

theorem cappedState_finite (p : Par) (Q D : ℕ) : Finite (CappedState p Q D) :=
  inferInstance

@[simp] theorem capProject_update {p : Par} (Q D : ℕ) (x : CappedSource p)
    (i : Fin p.M) (s : Site p.c p.N) :
    capProject Q D (Function.update x i s) =
      Function.update (capProject Q D x) i (capSite Q D s) := by
  classical
  funext j
  by_cases h : j = i
  · subst j
    simp [capProject]
  · simp [capProject, h]

/-- The exact source model on the saturation representatives. In particular,
merge retains the victim's capped external ledgers, just as the source does. -/
def cappedModel (p : Par) (Q D : ℕ) :
    SiteModel (CappedSite p.c p.N Q D) (Chem p.c) (Option (Fin p.c)) (Split p.c p.N) where
  rc s k := (cf3 p).rc (capRepresentSite s) k
  tc s k := capSite Q D ((cf3 p).tc (capRepresentSite s) k)
  rd s k := (cf3 p).rd (capRepresentSite s) k
  td s k := capSite Q D ((cf3 p).td (capRepresentSite s) k)
  ps s o := (cf3 p).ps (capRepresentSite s) o
  d1 s o := capSite Q D ((cf3 p).d1 (capRepresentSite s) o)
  d2 s o := capSite Q D ((cf3 p).d2 (capRepresentSite s) o)
  merge v d := capSite Q D ((cf3 p).merge (capRepresentSite v) (capRepresentSite d))

theorem cf3_rc_capped (p : Par) (Q D : ℕ) (s : Site p.c p.N) (k : Chem p.c) :
    (cf3 p).rc s k = (cappedModel p Q D).rc (capSite Q D s) k := rfl

theorem cf3_tc_capped (p : Par) (Q D : ℕ) (s : Site p.c p.N) (k : Chem p.c) :
    capSite Q D ((cf3 p).tc s k) =
      (cappedModel p Q D).tc (capSite Q D s) k := by
  classical
  cases k with
  | inl tj =>
      rcases tj with ⟨t, j⟩
      simp only [cf3, cappedModel]
      split_ifs <;> simp [capSite, capRepresentSite, capMap_update]
  | inr b =>
      cases b <;> simp [cappedModel, cf3, capSite, capRepresentSite]

theorem cf3_rd_capped (p : Par) (Q D : ℕ) (s : Site p.c p.N)
    (k : Option (Fin p.c)) :
    (cf3 p).rd s k = (cappedModel p Q D).rd (capSite Q D s) k := rfl

theorem cf3_td_capped (p : Par) (Q D : ℕ) (s : Site p.c p.N)
    (k : Option (Fin p.c)) :
    capSite Q D ((cf3 p).td s k) =
      (cappedModel p Q D).td (capSite Q D s) k := by
  classical
  cases k <;> simp [cappedModel, cf3, capSite, capRepresentSite, capMap_update]

theorem cf3_ps_capped (p : Par) (Q D : ℕ) (s : Site p.c p.N) (o : Split p.c p.N) :
    (cf3 p).ps s o = (cappedModel p Q D).ps (capSite Q D s) o := rfl

theorem cf3_d1_capped (p : Par) (Q D : ℕ) (s : Site p.c p.N) (o : Split p.c p.N) :
    capSite Q D ((cf3 p).d1 s o) =
      (cappedModel p Q D).d1 (capSite Q D s) o := by
  simp [cappedModel, cf3, capSite, capRepresentSite]

theorem cf3_d2_capped (p : Par) (Q D : ℕ) (s : Site p.c p.N) (o : Split p.c p.N) :
    capSite Q D ((cf3 p).d2 s o) =
      (cappedModel p Q D).d2 (capSite Q D s) o := by
  simp [cappedModel, cf3, capSite, capRepresentSite]

theorem cf3_merge_capped (p : Par) (Q D : ℕ) (v d : Site p.c p.N) :
    capSite Q D ((cf3 p).merge v d) =
      (cappedModel p Q D).merge (capSite Q D v) (capSite Q D d) := by
  simp [cappedModel, cf3, capSite, capRepresentSite]

/-- All capped observables intertwine with the literal source population
generator. No reset, split independence, or projected-law premise is assumed. -/
theorem cf3Gen_capped_project (p : Par) (Q D : ℕ)
    (f : CappedState p Q D → ℝ) (x : CappedSource p) :
    cf3Gen p (fun y => f (capProject Q D y)) x =
      popGen (cappedModel p Q D) p.M f (capProject Q D x) := by
  classical
  unfold cf3Gen popGen
  simp only [capProject_update, cf3_rc_capped p Q D, cf3_tc_capped,
    cf3_rd_capped p Q D, cf3_td_capped, cf3_ps_capped p Q D,
    cf3_d1_capped, cf3_d2_capped, cf3_merge_capped]
  rfl

def cappedGen (p : Par) (Q D : ℕ) (f : CappedState p Q D → ℝ)
    (x : CappedState p Q D) : ℝ :=
  cf3Gen p (fun y => f (capProject Q D y)) (capRepresent x)

theorem cappedGen_eq_popGen (p : Par) (Q D : ℕ)
    (f : CappedState p Q D → ℝ) (x : CappedState p Q D) :
    cappedGen p Q D f x = popGen (cappedModel p Q D) p.M f x := by
  rw [cappedGen, cf3Gen_capped_project, capProject_represent]

theorem cf3Gen_capped_lump (p : Par) (Q D : ℕ)
    (f : CappedState p Q D → ℝ) (x : CappedSource p) :
    cf3Gen p (fun y => f (capProject Q D y)) x =
      cappedGen p Q D f (capProject Q D x) := by
  rw [cf3Gen_capped_project, cappedGen_eq_popGen]

theorem cappedGen_isGen {p : Par} (hp : p.Valid) (Q D : ℕ) :
    IsGen (cf3Rate p) (cappedGen p Q D) where
  add := by
    intro f g x
    exact (cf3_isGen hp).add (fun y => f (capProject Q D y))
      (fun y => g (capProject Q D y)) (capRepresent x)
  smul := by
    intro c f x
    exact (cf3_isGen hp).smul c (fun y => f (capProject Q D y)) (capRepresent x)
  one := by
    intro x
    exact (cf3_isGen hp).one (capRepresent x)
  pos := by
    intro f hf x
    have h := (cf3_isGen hp).pos (fun y => f (capProject Q D y))
      (fun y => hf (capProject Q D y)) (capRepresent x)
    simpa only [capProject_represent, cappedGen] using h

/-! ## Mission observations and reset operations

The raw source formulas below are definitionally the `dead`, `okS`, `finalD`,
`resetQ`, and `resetAll` formulas in FunctionalCapacity.Mission. Keeping this
file's import at SiteCF3 avoids requiring the mission proof modules merely to
construct the finite source generator.
-/

theorem capSite_q_threshold {c N Q D m : ℕ} (hm : m ≤ Q)
    (s : Site c N) (j : Fin c) :
    m ≤ s.q j ↔ m ≤ ((capSite Q D s).q j : ℕ) :=
  (capNat_threshold hm (s.q j)).symm

theorem capSite_nd_threshold {c N Q D d : ℕ} (hd : d ≤ D) (s : Site c N) :
    d ≤ s.nd ↔ d ≤ ((capSite Q D s).nd : ℕ) :=
  (capNat_threshold hd s.nd).symm

def cappedDead {p : Par} {Q D : ℕ} (K : ℕ) (req : Finset (Fin p.c))
    (x : CappedState p Q D) : Prop :=
  ∃ i, ∃ j ∈ req, ((x i).a j : ℕ) < K

def cappedOkS {p : Par} {Q D : ℕ} (m : ℕ) (req : Finset (Fin p.c))
    (x : CappedState p Q D) : Prop :=
  ∀ i, ∀ j ∈ req, m ≤ ((x i).q j : ℕ)

def cappedFinalD {p : Par} {Q D : ℕ} (d : ℕ) (x : CappedState p Q D) : ℝ :=
  if ∀ i, d ≤ ((x i).nd : ℕ) then 1 else 0

theorem cap_dead_iff {p : Par} (Q D K : ℕ) (req : Finset (Fin p.c))
    (x : CappedSource p) :
    (∃ i, ∃ j ∈ req, ((x i).a j : ℕ) < K) ↔ cappedDead K req (capProject Q D x) :=
  Iff.rfl

theorem cap_okS_iff {p : Par} {Q D m : ℕ} (hm : m ≤ Q)
    (req : Finset (Fin p.c)) (x : CappedSource p) :
    (∀ i, ∀ j ∈ req, m ≤ (x i).q j) ↔ cappedOkS m req (capProject Q D x) := by
  simp only [cappedOkS, capProject, capSite, capNat_threshold hm]

theorem cap_finalD_eq {p : Par} {Q D d : ℕ} (hd : d ≤ D) (x : CappedSource p) :
    (if ∀ i, d ≤ (x i).nd then (1 : ℝ) else 0) =
      cappedFinalD d (capProject Q D x) := by
  simp only [cappedFinalD, capProject, capSite, capNat_threshold hd]

def cappedResetQ {p : Par} {Q D : ℕ} (x : CappedState p Q D) : CappedState p Q D :=
  fun i => { x i with q := fun _ => 0 }

def cappedResetAll {p : Par} {Q D : ℕ} (x : CappedState p Q D) : CappedState p Q D :=
  fun i => { x i with q := fun _ => 0, nd := 0 }

theorem cap_resetQ {p : Par} (Q D : ℕ) (x : CappedSource p) :
    capProject Q D (fun i => { x i with q := fun _ => 0 }) =
      cappedResetQ (capProject Q D x) := by
  funext i
  simp [capProject, capSite, cappedResetQ]

theorem cap_resetAll {p : Par} (Q D : ℕ) (x : CappedSource p) :
    capProject Q D (fun i => { x i with q := fun _ => 0, nd := 0 }) =
      cappedResetAll (capProject Q D x) := by
  funext i
  simp [capProject, capSite, cappedResetAll]

end

end CTMCHeredity20261019

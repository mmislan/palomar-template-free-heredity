module

public import proofs.FunctionalCapacity.SiteCF3

@[expose] public section

/-!
# The exact finite counts/fuel quotient of the literal CF3 generator

This file forgets only the unbounded external output/division ledgers. The
chemical counts, fuel state, all chemistry channels, the joint complementary
two-daughter split, and the uniformly selected victim are retained exactly.

The quotient identity is proved from the source transitions. No law or
generator-correspondence assumption is introduced. This quotient alone does
not retain service/output events or division-ledger events; those require a
marked path construction or a justified bounded ledger extension.
-/

namespace CTMCHeredity20261019

noncomputable section
open FunctionalCapacity

/-- The bounded chemical counts and one fuel bit of a compartment. -/
abbrev CoreSite (c N : ℕ) := (Fin c → Fin (N + 1)) × Bool

/-- The finite population core. -/
abbrev CoreState (p : Par) := Fin p.M → CoreSite p.c p.N

/-- The literal source state still has unbounded external ledgers. -/
abbrev SourceState (p : Par) := Fin p.M → Site p.c p.N

def siteProject {c N : ℕ} (s : Site c N) : CoreSite c N := (s.a, s.R)

/-- A representative, with both external ledgers initially zero. -/
def siteRepresent {c N : ℕ} (s : CoreSite c N) : Site c N where
  a := s.1
  R := s.2
  q := fun _ => 0
  nd := 0

def coreProject {p : Par} (x : SourceState p) : CoreState p :=
  fun i => siteProject (x i)

def coreRepresent {p : Par} (x : CoreState p) : SourceState p :=
  fun i => siteRepresent (x i)

@[simp] theorem siteProject_represent {c N : ℕ} (s : CoreSite c N) :
    siteProject (siteRepresent s) = s := by
  cases s
  rfl

@[simp] theorem coreProject_represent {p : Par} (x : CoreState p) :
    coreProject (coreRepresent x) = x := by
  funext i
  exact siteProject_represent (x i)

theorem coreProject_surjective (p : Par) :
    Function.Surjective (coreProject (p := p)) := by
  intro x
  exact ⟨coreRepresent x, coreProject_represent x⟩

/-- Finiteness is inherited from the bounded count vectors and fuel bits. -/
theorem coreState_finite (p : Par) : Finite (CoreState p) := inferInstance

/-- Projection commutes with replacing a site, including a division victim. -/
@[simp] theorem coreProject_update {p : Par} (x : SourceState p)
    (i : Fin p.M) (s : Site p.c p.N) :
    coreProject (Function.update x i s) =
      Function.update (coreProject x) i (siteProject s) := by
  classical
  funext j
  by_cases h : j = i
  · subst j
    simp [coreProject]
  · simp [coreProject, h]

/-- The projected site model is defined directly from the source representative.
Its division still has a single shared allocation and a complementary daughter. -/
def coreModel (p : Par) :
    SiteModel (CoreSite p.c p.N) (Chem p.c) (Option (Fin p.c)) (Split p.c p.N) where
  rc s k := (cf3 p).rc (siteRepresent s) k
  tc s k := siteProject ((cf3 p).tc (siteRepresent s) k)
  rd s k := (cf3 p).rd (siteRepresent s) k
  td s k := siteProject ((cf3 p).td (siteRepresent s) k)
  ps s o := (cf3 p).ps (siteRepresent s) o
  d1 s o := siteProject ((cf3 p).d1 (siteRepresent s) o)
  d2 s o := siteProject ((cf3 p).d2 (siteRepresent s) o)
  merge v d := siteProject ((cf3 p).merge (siteRepresent v) (siteRepresent d))

theorem cf3_rc_core (p : Par) (s : Site p.c p.N) (k : Chem p.c) :
    (cf3 p).rc s k = (coreModel p).rc (siteProject s) k := rfl

theorem cf3_tc_core (p : Par) (s : Site p.c p.N) (k : Chem p.c) :
    siteProject ((cf3 p).tc s k) = (coreModel p).tc (siteProject s) k := by
  cases k with
  | inl tj =>
      rcases tj with ⟨t, j⟩
      simp only [cf3, coreModel]
      split_ifs <;> rfl
  | inr b =>
      cases b <;> rfl

theorem cf3_rd_core (p : Par) (s : Site p.c p.N) (k : Option (Fin p.c)) :
    (cf3 p).rd s k = (coreModel p).rd (siteProject s) k := rfl

theorem cf3_td_core (p : Par) (s : Site p.c p.N) (k : Option (Fin p.c)) :
    siteProject ((cf3 p).td s k) = (coreModel p).td (siteProject s) k := by
  cases k <;> rfl

theorem cf3_ps_core (p : Par) (s : Site p.c p.N) (o : Split p.c p.N) :
    (cf3 p).ps s o = (coreModel p).ps (siteProject s) o := rfl

theorem cf3_d1_core (p : Par) (s : Site p.c p.N) (o : Split p.c p.N) :
    siteProject ((cf3 p).d1 s o) = (coreModel p).d1 (siteProject s) o := rfl

theorem cf3_d2_core (p : Par) (s : Site p.c p.N) (o : Split p.c p.N) :
    siteProject ((cf3 p).d2 s o) = (coreModel p).d2 (siteProject s) o := rfl

theorem cf3_merge_core (p : Par) (v d : Site p.c p.N) :
    siteProject ((cf3 p).merge v d) =
      (coreModel p).merge (siteProject v) (siteProject d) := rfl

/-- Exact source-level generator intertwining, proved channel by channel.
In particular, the two updates in a division remain simultaneous and share
the same original parent, split outcome, and victim. -/
theorem cf3Gen_project (p : Par) (f : CoreState p → ℝ) (x : SourceState p) :
    cf3Gen p (fun y => f (coreProject y)) x =
      popGen (coreModel p) p.M f (coreProject x) := by
  classical
  unfold cf3Gen popGen
  simp only [coreProject_update, cf3_rc_core, cf3_tc_core, cf3_rd_core,
    cf3_td_core, cf3_ps_core, cf3_d1_core, cf3_d2_core, cf3_merge_core]
  rfl

/-- The core generator is the original generator evaluated at the zero-ledger
representative. The preceding theorem proves this is independent of ledgers. -/
def coreGen (p : Par) (f : CoreState p → ℝ) (x : CoreState p) : ℝ :=
  cf3Gen p (fun y => f (coreProject y)) (coreRepresent x)

theorem coreGen_eq_popGen (p : Par) (f : CoreState p → ℝ) (x : CoreState p) :
    coreGen p f x = popGen (coreModel p) p.M f x := by
  rw [coreGen, cf3Gen_project, coreProject_represent]

/-- Full observable lumpability of the actual CF3 generator. -/
theorem cf3Gen_lump (p : Par) (f : CoreState p → ℝ) (x : SourceState p) :
    cf3Gen p (fun y => f (coreProject y)) x =
      coreGen p f (coreProject x) := by
  rw [cf3Gen_project, coreGen_eq_popGen]

/-- Any two source states with the same counts/fuel have identical generator
action on every core observable, regardless of their external ledgers. -/
theorem cf3Gen_ledger_independent (p : Par) (f : CoreState p → ℝ)
    (x y : SourceState p) (h : coreProject x = coreProject y) :
    cf3Gen p (fun z => f (coreProject z)) x =
      cf3Gen p (fun z => f (coreProject z)) y := by
  rw [cf3Gen_lump, cf3Gen_lump, h]

/-- The original source bound and positivity transfer to the finite quotient.
No additional validity, normalization, or stochastic-law hypothesis is assumed. -/
theorem coreGen_isGen {p : Par} (hp : p.Valid) :
    IsGen (cf3Rate p) (coreGen p) where
  add := by
    intro f g x
    exact (cf3_isGen hp).add (fun y => f (coreProject y))
      (fun y => g (coreProject y)) (coreRepresent x)
  smul := by
    intro c f x
    exact (cf3_isGen hp).smul c (fun y => f (coreProject y)) (coreRepresent x)
  one := by
    intro x
    exact (cf3_isGen hp).one (coreRepresent x)
  pos := by
    intro f hf x
    have h := (cf3_isGen hp).pos (fun y => f (coreProject y))
      (fun y => hf (coreProject y)) (coreRepresent x)
    simpa only [coreProject_represent, coreGen] using h

/-! ## The actual seed-free zero-count face

These are support statements, without any probabilistic interpretation assumed.
They can be combined with a constructed marked/uniformized path law.
-/

def ZeroCounts {c N : ℕ} (s : CoreSite c N) : Prop := ∀ j, s.1 j = 0

def CoreZero {p : Par} (x : CoreState p) : Prop := ∀ i, ZeroCounts (x i)

/-- When seeding is withdrawn, every count-changing chemical channel has
zero rate on the global zero-count face. Fuel transitions retain the face. -/
theorem coreModel_tc_zero {p : Par} (hε : p.ε = 0) (s : CoreSite p.c p.N)
    (hs : ZeroCounts s) (k : Chem p.c) (hk : (coreModel p).rc s k ≠ 0) :
    ZeroCounts ((coreModel p).tc s k) := by
  cases k with
  | inl tj =>
      rcases tj with ⟨t, j⟩
      exfalso
      apply hk
      simp [coreModel, cf3, siteRepresent, Site.u, Site.r, hε, hs j]
  | inr b =>
      cases b <;> exact hs

/-- Division bookkeeping and the triggered fuel discharge retain zero counts. -/
theorem coreModel_td_zero {p : Par} (s : CoreSite p.c p.N)
    (hs : ZeroCounts s) (k : Option (Fin p.c)) :
    ZeroCounts ((coreModel p).td s k) := by
  cases k <;> exact hs

/-- A positive/nonzero-weight split of a zero-count parent must allocate zero
to every first-daughter count. Unsupported nonzero allocations have exactly
zero binomial weight, rather than being deleted from the source outcome type. -/
theorem coreModel_ps_zero_support {p : Par} (s : CoreSite p.c p.N)
    (hs : ZeroCounts s) (o : Split p.c p.N)
    (ho : (coreModel p).ps s o ≠ 0) : ∀ j, o.1 j = 0 := by
  classical
  intro j
  by_contra hj
  have hjval : (o.1 j : ℕ) ≠ 0 := by
    intro h
    apply hj
    apply Fin.ext
    exact h
  have hjpos : 0 < (o.1 j : ℕ) := Nat.pos_of_ne_zero hjval
  have hfactor : ((Nat.choose (s.1 j) (o.1 j) : ℕ) : ℝ) /
      2 ^ (s.1 j : ℕ) = 0 := by
    simp [hs j, Nat.choose_eq_zero_of_lt hjpos]
  have hprod : (∏ k, ((Nat.choose (s.1 k) (o.1 k) : ℕ) : ℝ) /
      2 ^ (s.1 k : ℕ)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ j) hfactor
  apply ho
  change (∏ k, ((Nat.choose (s.1 k) (o.1 k) : ℕ) : ℝ) /
    2 ^ (s.1 k : ℕ)) * (1 / 2) = 0
  rw [hprod, zero_mul]

theorem coreModel_d1_zero {p : Par} (s : CoreSite p.c p.N)
    (hs : ZeroCounts s) (o : Split p.c p.N)
    (ho : (coreModel p).ps s o ≠ 0) :
    ZeroCounts ((coreModel p).d1 s o) := by
  exact coreModel_ps_zero_support s hs o ho

/-- The complementary daughter of a zero-count parent is zero even for
unsupported allocations, since the source uses truncated subtraction. -/
theorem coreModel_d2_zero {p : Par} (s : CoreSite p.c p.N)
    (hs : ZeroCounts s) (o : Split p.c p.N) :
    ZeroCounts ((coreModel p).d2 s o) := by
  intro j
  apply Fin.ext
  change (s.1 j : ℕ) - (o.1 j : ℕ) = 0
  simp [hs j]

theorem coreModel_merge_zero {p : Par} (v d : CoreSite p.c p.N)
    (hd : ZeroCounts d) : ZeroCounts ((coreModel p).merge v d) := hd

theorem CoreZero.update {p : Par} {x : CoreState p} (hx : CoreZero x)
    (i : Fin p.M) (s : CoreSite p.c p.N) (hs : ZeroCounts s) :
    CoreZero (Function.update x i s) := by
  classical
  intro v
  by_cases h : v = i
  · subst v
    simpa using hs
  · simpa [Function.update_of_ne h] using hx v

/-- Every nonzero-rate chemical jump preserves the seed-free zero-count face. -/
theorem coreChem_preserves_zero {p : Par} (hε : p.ε = 0)
    (x : CoreState p) (hx : CoreZero x) (i : Fin p.M) (k : Chem p.c)
    (hk : (coreModel p).rc (x i) k ≠ 0) :
    CoreZero (Function.update x i ((coreModel p).tc (x i) k)) :=
  hx.update i _ (coreModel_tc_zero hε (x i) (hx i) k hk)

/-- Both daughters, including the one simultaneously overwriting the victim,
preserve zero counts for every nonzero-weight source split. No independence
of daughter allocations is assumed or introduced. -/
theorem coreDivision_preserves_zero {p : Par} (x : CoreState p) (hx : CoreZero x)
    (i v : Fin p.M) (k : Option (Fin p.c)) (o : Split p.c p.N)
    (ho : (coreModel p).ps ((coreModel p).td (x i) k) o ≠ 0) :
    CoreZero (Function.update
      (Function.update x i ((coreModel p).d1 ((coreModel p).td (x i) k) o)) v
      ((coreModel p).merge (x v) ((coreModel p).d2 ((coreModel p).td (x i) k) o))) := by
  have htd := coreModel_td_zero (x i) (hx i) k
  have hd1 := coreModel_d1_zero _ htd o ho
  have hd2 := coreModel_d2_zero _ htd o
  exact (hx.update i _ hd1).update v _ (coreModel_merge_zero _ _ hd2)

/-- Source-derived generator invariance of the seed-free global zero face:
every observable vanishing on that face has zero generator there. This is an
actual CF3 count/fuel statement, including both daughters and victim overwrite. -/
theorem coreGen_zero_face {p : Par} (hε : p.ε = 0) (x : CoreState p)
    (hx : CoreZero x) (f : CoreState p → ℝ)
    (hf : ∀ y, CoreZero y → f y = 0) : coreGen p f x = 0 := by
  classical
  rw [coreGen_eq_popGen]
  unfold popGen
  apply Finset.sum_eq_zero
  intro i _
  conv_rhs => rw [← add_zero (0 : ℝ)]
  congr 1
  · apply Finset.sum_eq_zero
    intro k _
    by_cases hrc : (coreModel p).rc (x i) k = 0
    · rw [hrc, zero_mul]
    · rw [hf _ (coreChem_preserves_zero hε x hx i k hrc), hf x hx,
        sub_self, mul_zero]
  · apply Finset.sum_eq_zero
    intro k _
    have hinner : (∑ o, (coreModel p).ps ((coreModel p).td (x i) k) o *
        ∑ v, if v = i then 0 else (1 / ((p.M : ℝ) - 1)) *
          (f (Function.update
            (Function.update x i ((coreModel p).d1 ((coreModel p).td (x i) k) o)) v
            ((coreModel p).merge (x v)
              ((coreModel p).d2 ((coreModel p).td (x i) k) o))) - f x)) = 0 := by
      apply Finset.sum_eq_zero
      intro o _
      by_cases hps : (coreModel p).ps ((coreModel p).td (x i) k) o = 0
      · rw [hps, zero_mul]
      · have hvictim : (∑ v, if v = i then 0 else (1 / ((p.M : ℝ) - 1)) *
            (f (Function.update
              (Function.update x i ((coreModel p).d1 ((coreModel p).td (x i) k) o)) v
              ((coreModel p).merge (x v)
                ((coreModel p).d2 ((coreModel p).td (x i) k) o))) - f x)) = 0 := by
          apply Finset.sum_eq_zero
          intro v _
          split_ifs
          · rfl
          · rw [hf _ (coreDivision_preserves_zero x hx i v k o hps), hf x hx,
              sub_self, mul_zero]
        rw [hvictim, mul_zero]
    rw [hinner, mul_zero]

end

end CTMCHeredity20261019

module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Measurability
public import Mathlib.Tactic.Finiteness
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Functional capacity under fixed operating constraints: definitions

* `IsGen L G`      : `G` is a bounded Markov generator (acting on real functions) with rate bound `L`.
* `SubMarkov σ`    : a positive linear operator with `P 1 ≤ 1` (one tick of a killed uniformized chain).
* `stepK`          : uniformized tick of a generator killed on a set `dead`.
* `SubMarkov.ct`   : Poisson mixture of the tick powers, i.e. `E_x[f(X_T); not killed before T]` for the
                     continuous-time jump process with Poisson mean `μ = Λ T`.
* `SiteModel`, `popGen` : a population of `M` sites; each site has within-site channels and
                     division channels; a division splits the site state into two daughters, the first
                     stays, the second overwrites a uniformly chosen other site (`merge` keeps the
                     victim's external ledger).
* `cf3`            : the literal CF3 shared-fuel site model.
* `binE`, `siteOp` : binomial halving expectation and the per-site first-moment operator.
-/

namespace FunctionalCapacity

noncomputable section
open Finset

variable {σ : Type}

/-- `G` is a bounded generator with total rate at most `L`. -/
structure IsGen (L : ℝ) (G : (σ → ℝ) → σ → ℝ) : Prop where
  add : ∀ f g x, G (fun y => f y + g y) x = G f x + G g x
  smul : ∀ (c : ℝ) f x, G (fun y => c * f y) x = c * G f x
  one : ∀ x, G (fun _ => 1) x = 0
  pos : ∀ f, (∀ y, 0 ≤ f y) → ∀ x, 0 ≤ L * f x + G f x

/-- A sub-Markov operator on real functions of the state. -/
structure SubMarkov (σ : Type) where
  P : (σ → ℝ) → σ → ℝ
  mono : ∀ f g, (∀ y, f y ≤ g y) → ∀ x, P f x ≤ P g x
  add : ∀ f g x, P (fun y => f y + g y) x = P f x + P g x
  smul : ∀ (c : ℝ) f x, P (fun y => c * f y) x = c * P f x
  le_one : ∀ x, P (fun _ => 1) x ≤ 1

/-- Extension of `f` by zero on the killed set. -/
def kill (dead : σ → Prop) [DecidablePred dead] (f : σ → ℝ) : σ → ℝ :=
  fun y => if dead y then 0 else f y

/-- One tick of the uniformized chain of `G` (clock rate `Lam`), killed on `dead`. -/
def stepK (G : (σ → ℝ) → σ → ℝ) (Lam : ℝ) (dead : σ → Prop) [DecidablePred dead]
    (f : σ → ℝ) (x : σ) : ℝ :=
  if dead x then 0 else f x + G (kill dead f) x / Lam

/-- Poisson weights. -/
def pois (μ : ℝ) (n : ℕ) : ℝ := Real.exp (-μ) * (μ ^ n / n.factorial)

/-- `n` ticks. -/
def SubMarkov.iter (K : SubMarkov σ) : ℕ → (σ → ℝ) → σ → ℝ
  | 0, f => f
  | n + 1, f => K.iter n (K.P f)

/-- Continuous-time expectation: Poisson mixture of the tick powers (`μ = Lam * T`). -/
def SubMarkov.ct (K : SubMarkov σ) (μ : ℝ) (f : σ → ℝ) (x : σ) : ℝ :=
  ∑' n, pois μ n * K.iter n f x

/-- One mission block: run for time `T` (Poisson mean `μ`), require `ok` at the end, reset the
ledgers and continue with value `F`. -/
def block (K : SubMarkov σ) (μ : ℝ) (ok : σ → Prop) [DecidablePred ok] (reset : σ → σ)
    (F : σ → ℝ) : σ → ℝ :=
  K.ct μ (fun y => if ok y then F (reset y) else 0)

/-- `n` consecutive blocks followed by terminal value `F`. -/
def blocks (K : SubMarkov σ) (μ : ℝ) (ok : σ → Prop) [DecidablePred ok] (reset : σ → σ) :
    ℕ → (σ → ℝ) → σ → ℝ
  | 0, F => F
  | n + 1, F => block K μ ok reset (blocks K μ ok reset n F)

/-! ### Population of sites -/

/-- A site model: within-site channels `ιc`, division channels `ιd` (the site first moves to
`td`, then splits), split outcomes `ιs`. -/
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

/-- Generator of the population of `M` sites. -/
def popGen (m : SiteModel S ιc ιd ιs) (M : ℕ) (f : (Fin M → S) → ℝ) (x : Fin M → S) : ℝ :=
  ∑ i, ((∑ k, m.rc (x i) k * (f (Function.update x i (m.tc (x i) k)) - f x))
    + ∑ k, m.rd (x i) k * ∑ o, m.ps (m.td (x i) k) o *
        ∑ v, if v = i then 0 else
          (1 / ((M : ℝ) - 1)) *
            (f (Function.update (Function.update x i (m.d1 (m.td (x i) k) o)) v
                (m.merge (x v) (m.d2 (m.td (x i) k) o))) - f x))

/-! ### The CF3 site -/

/-- State of one compartment: core counts, fuel occupancy, external output ledger, division
ledger. -/
structure Site (c N : ℕ) where
  a : Fin c → Fin (N + 1)
  R : Bool
  q : Fin c → ℕ
  nd : ℕ

/-- Fixed operating parameters of the CF3 source. -/
structure Par where
  M : ℕ
  c : ℕ
  N : ℕ
  α : ℝ
  β : ℝ
  ε : ℝ

namespace Site

variable {c N : ℕ}

/-- occupancy fraction `a_j / N` -/
def u (s : Site c N) (j : Fin c) : ℝ := ((s.a j : ℕ) : ℝ) / N

/-- fuel occupancy as a real number -/
def r (s : Site c N) : ℝ := if s.R then 1 else 0

/-- add one molecule (the rate vanishes at `N`) -/
def inc (x : Fin (N + 1)) : Fin (N + 1) := ⟨min (x.val + 1) N, by omega⟩

/-- remove one molecule (the rate vanishes at `0`) -/
def dec (x : Fin (N + 1)) : Fin (N + 1) := ⟨x.val - 1, by omega⟩

/-- complementary allocation -/
def comp (x k : Fin (N + 1)) : Fin (N + 1) := ⟨x.val - k.val, by omega⟩

end Site

/-- within-site channels: `(0,j)` seed, `(1,j)` catalytic birth, `(2,j)` active turnover,
`(3,j)` passive decay, `(4,j)` ordinary job; `false` recharge, `true` unproductive discharge -/
abbrev Chem (c : ℕ) := (Fin 5 × Fin c) ⊕ Bool

/-- split outcomes: the allocation received by the first daughter and the fuel coin -/
abbrev Split (c N : ℕ) := (Fin c → Fin (N + 1)) × Bool

open Site in
/-- The literal CF3 site model. Division channels: `none` basal (rate 1), `some j` the
division-coupled job `j` (rate `u_j R`; it consumes the fuel and is recorded in the ledger). -/
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

/-- The CF3 population generator. -/
def cf3Gen (p : Par) : ((Fin p.M → Site p.c p.N) → ℝ) → (Fin p.M → Site p.c p.N) → ℝ :=
  popGen (cf3 p) p.M

/-- Rate bound of the CF3 population generator (per site: seeds, births, turnover, decay, jobs,
recharge/discharge, divisions). -/
def cf3Rate (p : Par) : ℝ :=
  p.M * (p.c * (p.ε + p.α * p.N + p.α / 2 * p.N + p.N + p.β) + p.β + (1 + p.c))

/-! ### Per-site first-moment operator -/

/-- expectation of `g` at a fair binomial half of `a` -/
def binE (g : ℕ → ℝ) (a : ℕ) : ℝ := ∑ k ∈ range (a + 1), ((a.choose k : ℕ) : ℝ) / 2 ^ a * g k

/-- First-moment (branching-drift) operator of one species at one site, for a potential
`W a R` of its count and the fuel state, under foreign discharge rate `Hf` and foreign trigger
rate `Uf`.  Basal divisions count both daughters and remove the site and one victim; triggered
divisions count both daughters and remove the site. -/
def siteOp (p : Par) (W : ℕ → Bool → ℝ) (a : ℕ) (R : Bool) (Hf Uf : ℝ) : ℝ :=
  let u : ℝ := (a : ℝ) / p.N
  if R then
    p.ε * (1 - u) * (W (a + 1) true - W a true)
      + p.α * a * (1 - u) * (W (a + 1) false - W a true)
      + p.α / 2 * a * (W (a - 1) false - W a true)
      + a * (W (a - 1) true - W a true)
      + (p.β * (1 + u) + Hf) * (W a false - W a true)
      + (binE (fun k => W k true) a + binE (fun k => W k false) a - 2 * W a true)
      + (u + Uf) * (2 * binE (fun k => W k false) a - W a true)
  else
    p.ε * (1 - u) * (W (a + 1) false - W a false)
      + a * (W (a - 1) false - W a false)
      + p.β * (W a true - W a false)
      + (2 * binE (fun k => W k false) a - 2 * W a false)

/-- A site certificate: a potential with branching drift `≤ -θ W + b` under every admissible
foreign load, at least one below the floor `K`. -/
structure SiteCert (p : Par) (K : ℕ) (W : ℕ → Bool → ℝ) (θ b Wmax : ℝ) : Prop where
  nonneg : ∀ a R, 0 ≤ W a R
  le_max : ∀ a R, W a R ≤ Wmax
  ge_one : ∀ a R, a < K → 1 ≤ W a R
  drift : ∀ a R Hf Uf, a ≤ p.N → 0 ≤ Uf → Uf ≤ (p.c : ℝ) - 1 → p.β * Uf ≤ Hf →
      Hf ≤ p.β * Uf + p.α * p.N * (9 / 16) * ((p.c : ℝ) - 1) →
      siteOp p W a R Hf Uf ≤ -θ * W a R + b

end

end FunctionalCapacity

module

public import proofs.FunctionalCapacity.Defs
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

/-!
# Functional capacity: sub-Markov kernel calculus

* `killed`            : the killed uniformized tick of a bounded generator is sub-Markov.
* `pois_*`            : Poisson weights (mass, generating function, mean).
* `SubMarkov.iter_*`  : monotonicity / linearity / bounds for tick powers.
* `Bdd`               : bounded functions, with closure lemmas.
* `SubMarkov.ct_*`    : the continuous-time operator (Poisson mixture) on bounded functions.
* `SubMarkov.ct_super`, `ct_sub_lower`, `ct_converse` : drift (super/sub-solution) bounds.
* `block_*`, `blocks_*` : mission blocks.
-/

namespace FunctionalCapacity

noncomputable section
open Finset

variable {σ : Type}

/-! ### Generators -/

theorem IsGen.zero {L : ℝ} {G : (σ → ℝ) → σ → ℝ} (hG : IsGen L G) (x : σ) :
    G (fun _ => 0) x = 0 := by
  have h := hG.smul 0 (fun _ => 0) x
  simpa using h

theorem IsGen.sub {L : ℝ} {G : (σ → ℝ) → σ → ℝ} (hG : IsGen L G) (f g : σ → ℝ) (x : σ) :
    G (fun y => f y - g y) x = G f x - G g x := by
  have h1 := hG.add f (fun y => (-1) * g y) x
  have h2 := hG.smul (-1) g x
  have e : (fun y => f y - g y) = fun y => f y + (-1) * g y := by
    funext y; ring
  rw [e, h1, h2]; ring

theorem kill_add (dead : σ → Prop) [DecidablePred dead] (f g : σ → ℝ) :
    kill dead (fun y => f y + g y) = fun y => kill dead f y + kill dead g y := by
  funext y
  simp only [kill]
  split_ifs <;> simp

theorem kill_smul (dead : σ → Prop) [DecidablePred dead] (c : ℝ) (f : σ → ℝ) :
    kill dead (fun y => c * f y) = fun y => c * kill dead f y := by
  funext y
  simp only [kill]
  split_ifs <;> simp

/-- The killed uniformized tick of a bounded generator is a sub-Markov operator. -/
def killed {L Lam : ℝ} {G : (σ → ℝ) → σ → ℝ} (hG : IsGen L G) (hLam : 0 < Lam) (hL : L ≤ Lam)
    (dead : σ → Prop) [DecidablePred dead] : SubMarkov σ where
  P := stepK G Lam dead
  mono := by
    intro f g h x
    simp only [stepK]
    split_ifs with hx
    · exact le_rfl
    · have hd : ∀ y, 0 ≤ kill dead g y - kill dead f y := by
        intro y
        simp only [kill]
        split_ifs
        · simp
        · linarith [h y]
      have hp : 0 ≤ L * (kill dead g x - kill dead f x)
          + G (fun y => kill dead g y - kill dead f y) x := hG.pos _ hd x
      rw [hG.sub] at hp
      have hk : kill dead g x - kill dead f x = g x - f x := by simp [kill, hx]
      rw [hk] at hp
      have h1 : L * (g x - f x) ≤ Lam * (g x - f x) :=
        mul_le_mul_of_nonneg_right hL (by linarith [h x])
      have h2 : G (kill dead f) x / Lam - G (kill dead g) x / Lam ≤ g x - f x := by
        rw [← sub_div, div_le_iff₀ hLam]
        linarith
      linarith
  add := by
    intro f g x
    simp only [stepK]
    rw [kill_add, hG.add]
    split_ifs
    · simp
    · ring
  smul := by
    intro c f x
    simp only [stepK]
    rw [kill_smul, hG.smul]
    split_ifs
    · simp
    · ring
  le_one := by
    intro x
    simp only [stepK]
    split_ifs with hx
    · exact zero_le_one
    · have e : kill dead (fun _ => (1 : ℝ)) = fun y => 1 - (if dead y then (1 : ℝ) else 0) := by
        funext y
        simp only [kill]
        split_ifs <;> simp
      have hp : 0 ≤ L * (if dead x then (1 : ℝ) else 0)
          + G (fun y => if dead y then (1 : ℝ) else 0) x :=
        hG.pos (fun y => if dead y then (1 : ℝ) else 0)
          (fun y => by
            show (0 : ℝ) ≤ if dead y then (1 : ℝ) else 0
            split_ifs <;> norm_num) x
      rw [ite_eq_right hx, mul_zero, zero_add] at hp
      have e2 := hG.sub (fun _ => (1 : ℝ)) (fun y => if dead y then (1 : ℝ) else 0) x
      rw [e, e2, hG.one]
      have h3 : (0 - G (fun y => if dead y then (1 : ℝ) else 0) x) / Lam ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) hLam.le
      linarith

@[simp] theorem killed_P {L Lam : ℝ} {G : (σ → ℝ) → σ → ℝ} (hG : IsGen L G) (hLam : 0 < Lam)
    (hL : L ≤ Lam) (dead : σ → Prop) [DecidablePred dead] :
    (killed hG hLam hL dead).P = stepK G Lam dead := rfl

/-! ### Poisson weights -/

theorem pois_nonneg {μ : ℝ} (hμ : 0 ≤ μ) (n : ℕ) : 0 ≤ pois μ n :=
  mul_nonneg (Real.exp_pos _).le (div_nonneg (pow_nonneg hμ n) (Nat.cast_nonneg _))

theorem pois_hasSum (μ : ℝ) : HasSum (pois μ) 1 := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) μ).mul_left (Real.exp (-μ))
  have e : Real.exp (-μ) * NormedSpace.exp μ = 1 := by
    rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]; simp
  rw [e] at h
  exact h

theorem pois_summable (μ : ℝ) : Summable (pois μ) := (pois_hasSum μ).summable

theorem pois_tsum (μ : ℝ) : ∑' n, pois μ n = 1 := (pois_hasSum μ).tsum_eq

theorem pois_pgf (μ s : ℝ) : HasSum (fun n => pois μ n * s ^ n) (Real.exp (μ * (s - 1))) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (μ * s)).mul_left (Real.exp (-μ))
  have e : Real.exp (-μ) * NormedSpace.exp (μ * s) = Real.exp (μ * (s - 1)) := by
    rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]
    congr 1
    ring
  rw [e] at h
  refine h.congr_fun ?_
  intro n
  unfold pois
  rw [mul_pow]
  ring

/-- The Poisson recursion `(n+1) p_{n+1} = μ p_n`. -/
theorem pois_succ_mul (μ : ℝ) (n : ℕ) : pois μ (n + 1) * ((n : ℝ) + 1) = μ * pois μ n := by
  unfold pois
  have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have h2 : ((n.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  field_simp

theorem pois_mean (μ : ℝ) : HasSum (fun n => pois μ n * (n : ℝ)) μ := by
  rw [← hasSum_nat_add_iff' 1]
  have e : (fun n : ℕ => pois μ (n + 1) * ((n + 1 : ℕ) : ℝ)) = fun n => μ * pois μ n := by
    funext n
    push_cast
    exact pois_succ_mul μ n
  rw [e]
  have h0 := (pois_hasSum μ).mul_left μ
  rw [mul_one] at h0
  have e2 : μ - ∑ i ∈ range 1, pois μ i * (i : ℝ) = μ := by simp
  rw [e2]
  exact h0

/-! ### Bounded functions -/

/-- `f` is a bounded function. -/
def Bdd (f : σ → ℝ) : Prop := ∃ B, ∀ y, |f y| ≤ B

namespace Bdd

theorem of_abs {f : σ → ℝ} {B : ℝ} (h : ∀ y, |f y| ≤ B) : Bdd f := ⟨B, h⟩

theorem const (c : ℝ) : Bdd (fun _ : σ => c) := ⟨|c|, fun _ => le_rfl⟩

theorem of_le {f : σ → ℝ} {c : ℝ} (h0 : ∀ y, 0 ≤ f y) (h1 : ∀ y, f y ≤ c) : Bdd f :=
  ⟨c, fun y => by rw [abs_of_nonneg (h0 y)]; exact h1 y⟩

theorem add {f g : σ → ℝ} (hf : Bdd f) (hg : Bdd g) : Bdd (fun y => f y + g y) := by
  obtain ⟨B, hB⟩ := hf
  obtain ⟨B', hB'⟩ := hg
  refine ⟨B + B', fun y => ?_⟩
  have h1 := abs_le.mp (hB y)
  have h2 := abs_le.mp (hB' y)
  rw [abs_le]
  constructor <;> linarith

theorem sub {f g : σ → ℝ} (hf : Bdd f) (hg : Bdd g) : Bdd (fun y => f y - g y) := by
  obtain ⟨B, hB⟩ := hf
  obtain ⟨B', hB'⟩ := hg
  refine ⟨B + B', fun y => ?_⟩
  have h1 := abs_le.mp (hB y)
  have h2 := abs_le.mp (hB' y)
  rw [abs_le]
  constructor <;> linarith

theorem smul (c : ℝ) {f : σ → ℝ} (hf : Bdd f) : Bdd (fun y => c * f y) := by
  obtain ⟨B, hB⟩ := hf
  exact ⟨|c| * B, fun y => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hB y) (abs_nonneg c)⟩

theorem ite (p : σ → Prop) [DecidablePred p] {f g : σ → ℝ} (hf : Bdd f) (hg : Bdd g) :
    Bdd (fun y => if p y then f y else g y) := by
  obtain ⟨B, hB⟩ := hf
  obtain ⟨B', hB'⟩ := hg
  refine ⟨max B B', fun y => ?_⟩
  show |if p y then f y else g y| ≤ max B B'
  split_ifs
  · exact le_max_of_le_left (hB y)
  · exact le_max_of_le_right (hB' y)

theorem comp {τ : Type} {f : σ → ℝ} (hf : Bdd f) (r : τ → σ) : Bdd (fun y => f (r y)) := by
  obtain ⟨B, hB⟩ := hf
  exact ⟨B, fun y => hB (r y)⟩

theorem sum {ι : Type} (s : Finset ι) (F : ι → σ → ℝ) (hF : ∀ i ∈ s, Bdd (F i)) :
    Bdd (fun y => ∑ i ∈ s, F i y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Bdd.const (σ := σ) 0)
  | insert a s ha ih =>
    have h1 := hF a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
    simp only [Finset.sum_insert ha]
    exact h1.add h2

end Bdd

namespace SubMarkov

variable (K : SubMarkov σ)

/-! ### Tick powers -/

theorem iter_succ (n : ℕ) (f : σ → ℝ) : K.iter (n + 1) f = K.iter n (K.P f) := rfl

theorem iter_mono {f g : σ → ℝ} (n : ℕ) (h : ∀ y, f y ≤ g y) (x : σ) :
    K.iter n f x ≤ K.iter n g x := by
  induction n generalizing f g with
  | zero => exact h x
  | succ n ih =>
    rw [K.iter_succ, K.iter_succ]
    exact ih (K.mono f g h)

theorem iter_add (n : ℕ) (f g : σ → ℝ) (x : σ) :
    K.iter n (fun y => f y + g y) x = K.iter n f x + K.iter n g x := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    have e : K.P (fun y => f y + g y) = fun y => K.P f y + K.P g y := funext (K.add f g)
    show K.iter n (K.P fun y => f y + g y) x = K.iter n (K.P f) x + K.iter n (K.P g) x
    rw [e, ih]

theorem iter_smul (n : ℕ) (c : ℝ) (f : σ → ℝ) (x : σ) :
    K.iter n (fun y => c * f y) x = c * K.iter n f x := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    have e : K.P (fun y => c * f y) = fun y => c * K.P f y := funext (K.smul c f)
    show K.iter n (K.P fun y => c * f y) x = c * K.iter n (K.P f) x
    rw [e, ih]

theorem iter_sub (n : ℕ) (f g : σ → ℝ) (x : σ) :
    K.iter n (fun y => f y - g y) x = K.iter n f x - K.iter n g x := by
  have e : (fun y => f y - g y) = fun y => f y + (-1) * g y := by
    funext y; ring
  rw [e, K.iter_add n f (fun y => (-1) * g y) x, K.iter_smul n (-1) g x]
  ring

theorem P_const_le {c : ℝ} (hc : 0 ≤ c) (x : σ) : K.P (fun _ => c) x ≤ c := by
  have h := K.smul c (fun _ => 1) x
  simp only [mul_one] at h
  rw [h]
  have h2 := mul_le_mul_of_nonneg_left (K.le_one x) hc
  linarith

theorem iter_const_le {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (x : σ) : K.iter n (fun _ => c) x ≤ c := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [K.iter_succ]
    exact le_trans (K.iter_mono n (fun y => K.P_const_le hc y) x) ih

theorem iter_const_zero (n : ℕ) (x : σ) : K.iter n (fun _ => 0) x = 0 := by
  have h := K.iter_smul n 0 (fun _ => 0) x
  simpa using h

theorem iter_nonneg {f : σ → ℝ} (h : ∀ y, 0 ≤ f y) (n : ℕ) (x : σ) : 0 ≤ K.iter n f x := by
  have h1 := K.iter_mono (f := fun _ => 0) (g := f) n h x
  rwa [K.iter_const_zero] at h1

theorem iter_abs_le {f : σ → ℝ} {B : ℝ} (h : ∀ y, |f y| ≤ B) (n : ℕ) (x : σ) :
    |K.iter n f x| ≤ B := by
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (h x)
  have h1 := K.iter_mono (f := f) (g := fun _ => B) n (fun y => (abs_le.mp (h y)).2) x
  have h2 := K.iter_mono (f := fun _ => (-1) * B) (g := f) n
    (fun y => by linarith [(abs_le.mp (h y)).1]) x
  rw [K.iter_smul n (-1) (fun _ => B) x] at h2
  have h3 := K.iter_const_le hB n x
  rw [abs_le]
  constructor <;> linarith

/-! ### The continuous-time operator -/

theorem ct_summable {f : σ → ℝ} (hf : Bdd f) (μ : ℝ) (x : σ) :
    Summable fun n => pois μ n * K.iter n f x := by
  obtain ⟨B, hB⟩ := hf
  refine Summable.of_norm_bounded (g := fun n => |pois μ n| * B)
    ((pois_summable μ).abs.mul_right B) ?_
  intro n
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (K.iter_abs_le hB n x) (abs_nonneg _)

theorem ct_hasSum {f : σ → ℝ} (hf : Bdd f) (μ : ℝ) (x : σ) :
    HasSum (fun n => pois μ n * K.iter n f x) (K.ct μ f x) :=
  (K.ct_summable hf μ x).hasSum

theorem ct_add {f g : σ → ℝ} {μ : ℝ} (hf : Bdd f) (hg : Bdd g) (x : σ) :
    K.ct μ (fun y => f y + g y) x = K.ct μ f x + K.ct μ g x := by
  simp only [ct]
  rw [← (K.ct_summable hf μ x).tsum_add (K.ct_summable hg μ x)]
  refine tsum_congr fun n => ?_
  rw [K.iter_add]; ring

theorem ct_sub {f g : σ → ℝ} {μ : ℝ} (hf : Bdd f) (hg : Bdd g) (x : σ) :
    K.ct μ (fun y => f y - g y) x = K.ct μ f x - K.ct μ g x := by
  simp only [ct]
  rw [← (K.ct_summable hf μ x).tsum_sub (K.ct_summable hg μ x)]
  refine tsum_congr fun n => ?_
  rw [K.iter_sub]; ring

theorem ct_smul (c : ℝ) (f : σ → ℝ) (μ : ℝ) (x : σ) :
    K.ct μ (fun y => c * f y) x = c * K.ct μ f x := by
  simp only [ct]
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [K.iter_smul]; ring

theorem ct_const_zero (μ : ℝ) (x : σ) : K.ct μ (fun _ => 0) x = 0 := by
  simp [ct, K.iter_const_zero]

theorem ct_sum {ι : Type} {μ : ℝ} (s : Finset ι) (F : ι → σ → ℝ) (hF : ∀ i ∈ s, Bdd (F i))
    (x : σ) : K.ct μ (fun y => ∑ i ∈ s, F i y) x = ∑ i ∈ s, K.ct μ (F i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ct, K.iter_const_zero]
  | insert a s ha ih =>
    have h1 := hF a (Finset.mem_insert_self a s)
    have hF' : ∀ i ∈ s, Bdd (F i) := fun i hi => hF i (Finset.mem_insert_of_mem hi)
    simp only [Finset.sum_insert ha]
    rw [K.ct_add h1 (Bdd.sum s F hF') x, ih hF']

theorem ct_mono {f g : σ → ℝ} {μ : ℝ} (hμ : 0 ≤ μ) (hf : Bdd f) (hg : Bdd g)
    (h : ∀ y, f y ≤ g y) (x : σ) : K.ct μ f x ≤ K.ct μ g x := by
  have hterm : ∀ n, pois μ n * K.iter n f x ≤ pois μ n * K.iter n g x := fun n =>
    mul_le_mul_of_nonneg_left (K.iter_mono n h x) (pois_nonneg hμ n)
  exact hasSum_le hterm (K.ct_hasSum hf μ x) (K.ct_hasSum hg μ x)

theorem ct_nonneg {f : σ → ℝ} {μ : ℝ} (hμ : 0 ≤ μ) (h : ∀ y, 0 ≤ f y) (x : σ) :
    0 ≤ K.ct μ f x :=
  tsum_nonneg fun n => mul_nonneg (pois_nonneg hμ n) (K.iter_nonneg h n x)

theorem ct_le {f : σ → ℝ} {μ c : ℝ} (hμ : 0 ≤ μ) (hc : 0 ≤ c) (h0 : ∀ y, 0 ≤ f y)
    (h : ∀ y, f y ≤ c) (x : σ) : K.ct μ f x ≤ c := by
  have hterm : ∀ n, pois μ n * K.iter n f x ≤ pois μ n * c := fun n =>
    mul_le_mul_of_nonneg_left (le_trans (K.iter_mono n h x) (K.iter_const_le hc n x))
      (pois_nonneg hμ n)
  have hle := hasSum_le hterm (K.ct_hasSum (Bdd.of_le h0 h) μ x) ((pois_hasSum μ).mul_right c)
  rwa [one_mul] at hle

theorem ct_abs_le {f : σ → ℝ} {μ B : ℝ} (hμ : 0 ≤ μ) (h : ∀ y, |f y| ≤ B) (x : σ) :
    |K.ct μ f x| ≤ B := by
  have hterm : ∀ n, |pois μ n * K.iter n f x| ≤ pois μ n * B := fun n => by
    rw [abs_mul, abs_of_nonneg (pois_nonneg hμ n)]
    exact mul_le_mul_of_nonneg_left (K.iter_abs_le h n x) (pois_nonneg hμ n)
  have hR := (pois_hasSum μ).mul_right B
  rw [one_mul] at hR
  have hf := K.ct_hasSum ⟨B, h⟩ μ x
  have h1 := hasSum_le (fun n => (abs_le.mp (hterm n)).2) hf hR
  have h2 := hasSum_le (fun n => (abs_le.mp (hterm n)).1) hR.neg hf
  rw [abs_le]
  exact ⟨h2, h1⟩

/-! ### Supersolution decay -/

theorem iter_super {V : σ → ℝ} {θ b : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hb : 0 ≤ b)
    (h : ∀ x, K.P V x ≤ (1 - θ) * V x + b) (n : ℕ) (x : σ) :
    K.iter n V x ≤ (1 - θ) ^ n * V x + n * b := by
  induction n with
  | zero => simp [iter]
  | succ n ih =>
    have h1 : K.iter n (K.P V) x ≤ K.iter n (fun y => (1 - θ) * V y + b) x :=
      K.iter_mono n h x
    rw [K.iter_add n (fun y => (1 - θ) * V y) (fun _ => b) x, K.iter_smul n (1 - θ) V x] at h1
    have h2 := K.iter_const_le hb n x
    have h3 := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hθ1)
    have h4 : 0 ≤ θ * ((n : ℝ) * b) := mul_nonneg hθ0 (mul_nonneg (Nat.cast_nonneg n) hb)
    rw [K.iter_succ, pow_succ]
    push_cast
    nlinarith [h1, h2, h3, h4]

/-- **Supersolution decay**: a per-tick drift `P V ≤ (1-θ) V + b` gives exponential decay of the
continuous-time expectation up to the accumulated source. -/
theorem ct_super {V : σ → ℝ} {θ b B μ : ℝ} (hV0 : ∀ y, 0 ≤ V y) (hVB : ∀ y, V y ≤ B)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hb : 0 ≤ b) (hμ : 0 ≤ μ)
    (h : ∀ x, K.P V x ≤ (1 - θ) * V x + b) (x : σ) :
    K.ct μ V x ≤ Real.exp (-(θ * μ)) * V x + b * μ := by
  have hbd : Bdd V := Bdd.of_le hV0 hVB
  have hR : HasSum (fun n => pois μ n * (1 - θ) ^ n * V x + b * (pois μ n * (n : ℝ)))
      (Real.exp (μ * (1 - θ - 1)) * V x + b * μ) :=
    ((pois_pgf μ (1 - θ)).mul_right (V x)).add ((pois_mean μ).mul_left b)
  have hterm : ∀ n, pois μ n * K.iter n V x
      ≤ pois μ n * (1 - θ) ^ n * V x + b * (pois μ n * (n : ℝ)) := by
    intro n
    have h1 := mul_le_mul_of_nonneg_left (K.iter_super hθ0 hθ1 hb h n x) (pois_nonneg hμ n)
    calc pois μ n * K.iter n V x ≤ pois μ n * ((1 - θ) ^ n * V x + n * b) := h1
      _ = pois μ n * (1 - θ) ^ n * V x + b * (pois μ n * (n : ℝ)) := by ring
  have hle := hasSum_le hterm (K.ct_hasSum hbd μ x) hR
  have e : μ * (1 - θ - 1) = -(θ * μ) := by ring
  rw [e] at hle
  exact hle

/-! ### Subsolution lower bound -/

theorem iter_sub_lower {g : σ → ℝ} {b : ℝ} (hb : 0 ≤ b) (h : ∀ x, g x - b ≤ K.P g x)
    (n : ℕ) (x : σ) : g x - n * b ≤ K.iter n g x := by
  induction n with
  | zero => simp [iter]
  | succ n ih =>
    have h1 : K.iter n (fun y => g y - b) x ≤ K.iter n (K.P g) x := K.iter_mono n h x
    rw [K.iter_sub n g (fun _ => b) x] at h1
    have h2 := K.iter_const_le hb n x
    rw [K.iter_succ]
    push_cast
    linarith

/-- **Subsolution lower bound**: a per-tick loss of at most `b` costs at most `b μ`. -/
theorem ct_sub_lower {g : σ → ℝ} {b B μ : ℝ} (hg : ∀ y, |g y| ≤ B) (hb : 0 ≤ b) (hμ : 0 ≤ μ)
    (h : ∀ x, g x - b ≤ K.P g x) (x : σ) : g x - b * μ ≤ K.ct μ g x := by
  have hR : HasSum (fun n => pois μ n * g x - b * (pois μ n * (n : ℝ))) (1 * g x - b * μ) :=
    ((pois_hasSum μ).mul_right (g x)).sub ((pois_mean μ).mul_left b)
  have hterm : ∀ n, pois μ n * g x - b * (pois μ n * (n : ℝ)) ≤ pois μ n * K.iter n g x := by
    intro n
    have h1 := mul_le_mul_of_nonneg_left (K.iter_sub_lower hb h n x) (pois_nonneg hμ n)
    calc pois μ n * g x - b * (pois μ n * (n : ℝ)) = pois μ n * (g x - n * b) := by ring
      _ ≤ pois μ n * K.iter n g x := h1
  have hle := hasSum_le hterm hR (K.ct_hasSum ⟨B, hg⟩ μ x)
  linarith

/-! ### Expectation converse -/

/-- **Expectation converse.** If the resource `Z` pays `κ` per tick while alive (`al`), up to a
source `b0`, and the success indicator `g` needs `m0` units of `Z`, then the success probability
at Poisson mean `μ` is at most `(Z x + b0 μ) / (m0 + κ μ)`. -/
theorem ct_converse' {Z al g : σ → ℝ} {κ b0 m0 μ : ℝ}
    (hal0 : ∀ y, 0 ≤ al y) (hal1 : ∀ y, al y ≤ 1)
    (hg0 : ∀ y, 0 ≤ g y) (hgal : ∀ y, g y ≤ al y) (hκ : 0 ≤ κ) (hb0 : 0 ≤ b0)
    (hμ : 0 ≤ μ)
    (hP : ∀ x, K.P Z x + κ * al x ≤ Z x + b0) (hPal : ∀ x, K.P al x ≤ al x)
    (hgZ : ∀ y, m0 * g y ≤ Z y) (x : σ) :
    K.ct μ g x * (m0 + κ * μ) ≤ Z x + b0 * μ := by
  have hbg : Bdd g := Bdd.of_le hg0 (fun y => le_trans (hgal y) (hal1 y))
  have hp_step : ∀ n, K.iter (n + 1) al x ≤ K.iter n al x := fun n => by
    rw [K.iter_succ]; exact K.iter_mono n hPal x
  have hp_anti : ∀ n k, k ≤ n → K.iter n al x ≤ K.iter k al x := by
    intro n k hkn
    induction n, hkn using Nat.le_induction with
    | base => exact le_rfl
    | succ n _ ih => exact le_trans (hp_step n) ih
  have hp0 : ∀ n, 0 ≤ K.iter n al x := fun n => K.iter_nonneg hal0 n x
  have hp1 : ∀ n, K.iter n al x ≤ 1 := fun n =>
    le_trans (K.iter_mono n hal1 x) (K.iter_const_le zero_le_one n x)
  have hgp : ∀ n, K.iter n g x ≤ K.iter n al x := fun n => K.iter_mono n hgal x
  have hmE : ∀ n, m0 * K.iter n g x ≤ K.iter n Z x := by
    intro n
    have h1 := K.iter_mono n hgZ x
    rwa [K.iter_smul n m0 g x] at h1
  have hE : ∀ n, K.iter (n + 1) Z x + κ * K.iter n al x ≤ K.iter n Z x + b0 := by
    intro n
    have h1 : K.iter n (K.P Z) x ≤ K.iter n (fun y => (Z y + b0) - κ * al y) x :=
      K.iter_mono n (fun y => by linarith [hP y]) x
    rw [K.iter_sub n (fun y => Z y + b0) (fun y => κ * al y) x,
      K.iter_add n Z (fun _ => b0) x, K.iter_smul n κ al x] at h1
    have h2 := K.iter_const_le hb0 n x
    rw [K.iter_succ]
    linarith
  have hT : ∀ n, K.iter n Z x + κ * ∑ k ∈ range n, K.iter k al x ≤ Z x + n * b0 := by
    intro n
    induction n with
    | zero => simp [iter]
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add]
      push_cast
      linarith [hE n]
  have hS : ∀ n : ℕ, ((n : ℝ) + 1) * K.iter n al x ≤ ∑ k ∈ range (n + 1), K.iter k al x := by
    intro n
    have h := Finset.card_nsmul_le_sum (range (n + 1)) (fun k => K.iter k al x) (K.iter n al x)
      (fun k hk => hp_anti n k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
    simpa [nsmul_eq_mul] using h
  have hS0 : ∀ n, 0 ≤ ∑ k ∈ range n, K.iter k al x := fun n =>
    Finset.sum_nonneg (fun k _ => hp0 k)
  have hS1 : ∀ n, ∑ k ∈ range n, K.iter k al x ≤ n := by
    intro n
    have h := Finset.sum_le_card_nsmul (range n) (fun k => K.iter k al x) 1 (fun k _ => hp1 k)
    simpa using h
  have hsumS : Summable fun n => pois μ n * ∑ k ∈ range n, K.iter k al x :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (pois_nonneg hμ n) (hS0 n))
      (fun n => mul_le_mul_of_nonneg_left (hS1 n) (pois_nonneg hμ n)) (pois_mean μ).summable
  have hA := hsumS.hasSum
  have hA' : HasSum (fun n => pois μ (n + 1) * ∑ k ∈ range (n + 1), K.iter k al x)
      (∑' n, pois μ n * ∑ k ∈ range n, K.iter k al x) := by
    have h := (hasSum_nat_add_iff' (f := fun n => pois μ n * ∑ k ∈ range n, K.iter k al x) 1).2 hA
    simpa using h
  have hG := (K.ct_hasSum hbg μ x).mul_left μ
  have hterm1 : ∀ n, μ * (pois μ n * K.iter n g x)
      ≤ pois μ (n + 1) * ∑ k ∈ range (n + 1), K.iter k al x := by
    intro n
    have h1 := mul_le_mul_of_nonneg_left (hS n) (pois_nonneg hμ (n + 1))
    have h2 := mul_le_mul_of_nonneg_left (hgp n) (mul_nonneg hμ (pois_nonneg hμ n))
    have e := pois_succ_mul μ n
    calc μ * (pois μ n * K.iter n g x) = μ * pois μ n * K.iter n g x := by ring
      _ ≤ μ * pois μ n * K.iter n al x := h2
      _ = pois μ (n + 1) * (((n : ℝ) + 1) * K.iter n al x) := by rw [← e]; ring
      _ ≤ pois μ (n + 1) * ∑ k ∈ range (n + 1), K.iter k al x := h1
  have hA1 : μ * K.ct μ g x ≤ ∑' n, pois μ n * ∑ k ∈ range n, K.iter k al x :=
    hasSum_le hterm1 hG hA'
  have hL : HasSum (fun n => m0 * (pois μ n * K.iter n g x)
        + κ * (pois μ n * ∑ k ∈ range n, K.iter k al x))
      (m0 * K.ct μ g x + κ * ∑' n, pois μ n * ∑ k ∈ range n, K.iter k al x) :=
    ((K.ct_hasSum hbg μ x).mul_left m0).add (hA.mul_left κ)
  have hR : HasSum (fun n => pois μ n * Z x + b0 * (pois μ n * (n : ℝ))) (1 * Z x + b0 * μ) :=
    ((pois_hasSum μ).mul_right (Z x)).add ((pois_mean μ).mul_left b0)
  have hterm2 : ∀ n, m0 * (pois μ n * K.iter n g x)
        + κ * (pois μ n * ∑ k ∈ range n, K.iter k al x)
      ≤ pois μ n * Z x + b0 * (pois μ n * (n : ℝ)) := by
    intro n
    have h1 := mul_le_mul_of_nonneg_left (hmE n) (pois_nonneg hμ n)
    have h2 := mul_le_mul_of_nonneg_left (hT n) (pois_nonneg hμ n)
    calc m0 * (pois μ n * K.iter n g x) + κ * (pois μ n * ∑ k ∈ range n, K.iter k al x)
        = pois μ n * (m0 * K.iter n g x)
          + pois μ n * (κ * ∑ k ∈ range n, K.iter k al x) := by ring
      _ ≤ pois μ n * (K.iter n Z x + κ * ∑ k ∈ range n, K.iter k al x) := by
          rw [mul_add]; linarith
      _ ≤ pois μ n * (Z x + n * b0) := h2
      _ = pois μ n * Z x + b0 * (pois μ n * (n : ℝ)) := by ring
  have hmain := hasSum_le hterm2 hL hR
  have hκA := mul_le_mul_of_nonneg_left hA1 hκ
  linarith

/-- `ct_converse'` with the full (redundant) hypothesis list: nonnegativity/boundedness of `Z`
and `0 ≤ m0` are not needed for the inequality. -/
theorem ct_converse {Z al g : σ → ℝ} {κ b0 m0 B μ : ℝ}
    (hZ0 : ∀ y, 0 ≤ Z y) (hZB : ∀ y, Z y ≤ B) (hal0 : ∀ y, 0 ≤ al y) (hal1 : ∀ y, al y ≤ 1)
    (hg0 : ∀ y, 0 ≤ g y) (hgal : ∀ y, g y ≤ al y) (hκ : 0 ≤ κ) (hb0 : 0 ≤ b0) (hm0 : 0 ≤ m0)
    (hμ : 0 ≤ μ)
    (hP : ∀ x, K.P Z x + κ * al x ≤ Z x + b0) (hPal : ∀ x, K.P al x ≤ al x)
    (hgZ : ∀ y, m0 * g y ≤ Z y) (x : σ) :
    K.ct μ g x * (m0 + κ * μ) ≤ Z x + b0 * μ := by
  have _h := And.intro (And.intro hZ0 hZB) hm0
  exact K.ct_converse' hal0 hal1 hg0 hgal hκ hb0 hμ hP hPal hgZ x

end SubMarkov

/-! ### Mission blocks -/

section Blocks

variable (K : SubMarkov σ) {μ : ℝ} {ok : σ → Prop} [DecidablePred ok] {reset : σ → σ}

theorem Bdd.blockArg {F : σ → ℝ} (hF : Bdd F) :
    Bdd (fun y => if ok y then F (reset y) else 0) :=
  Bdd.ite ok (hF.comp reset) (Bdd.const 0)

theorem block_nonneg {F : σ → ℝ} (hμ : 0 ≤ μ) (h0 : ∀ y, 0 ≤ F y) (x : σ) :
    0 ≤ block K μ ok reset F x := by
  have hn : ∀ y, 0 ≤ (if ok y then F (reset y) else 0) := by
    intro y
    split_ifs
    · exact h0 _
    · exact le_rfl
  exact K.ct_nonneg hμ hn x

theorem block_le_one {F : σ → ℝ} (hμ : 0 ≤ μ) (h0 : ∀ y, 0 ≤ F y) (h1 : ∀ y, F y ≤ 1) (x : σ) :
    block K μ ok reset F x ≤ 1 := by
  have hn : ∀ y, 0 ≤ (if ok y then F (reset y) else 0) := by
    intro y
    split_ifs
    · exact h0 _
    · exact le_rfl
  have hl : ∀ y, (if ok y then F (reset y) else 0) ≤ 1 := by
    intro y
    split_ifs
    · exact h1 _
    · exact zero_le_one
  exact K.ct_le hμ zero_le_one hn hl x

theorem block_mono {F F' : σ → ℝ} (hμ : 0 ≤ μ) (hF : Bdd F) (hF' : Bdd F')
    (h : ∀ y, F y ≤ F' y) (x : σ) : block K μ ok reset F x ≤ block K μ ok reset F' x := by
  have hm : ∀ y, (if ok y then F (reset y) else 0) ≤ (if ok y then F' (reset y) else 0) := by
    intro y
    split_ifs
    · exact h _
    · exact le_rfl
  exact K.ct_mono hμ hF.blockArg hF'.blockArg hm x

theorem blocks_nonneg {F : σ → ℝ} (hμ : 0 ≤ μ) (h0 : ∀ y, 0 ≤ F y) (n : ℕ) (x : σ) :
    0 ≤ blocks K μ ok reset n F x := by
  induction n generalizing x with
  | zero => exact h0 x
  | succ n ih =>
    show 0 ≤ block K μ ok reset (blocks K μ ok reset n F) x
    exact block_nonneg K hμ ih x

theorem blocks_le_one {F : σ → ℝ} (hμ : 0 ≤ μ) (h0 : ∀ y, 0 ≤ F y) (h1 : ∀ y, F y ≤ 1)
    (n : ℕ) (x : σ) : blocks K μ ok reset n F x ≤ 1 := by
  induction n generalizing x with
  | zero => exact h1 x
  | succ n ih =>
    show block K μ ok reset (blocks K μ ok reset n F) x ≤ 1
    exact block_le_one K hμ (fun y => blocks_nonneg K hμ h0 n y) ih x

end Blocks

end

end FunctionalCapacity

#print axioms FunctionalCapacity.SubMarkov.ct_super
#print axioms FunctionalCapacity.SubMarkov.ct_sub_lower

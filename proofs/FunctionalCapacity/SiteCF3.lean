module

public import proofs.FunctionalCapacity.Pop

@[expose] public section

/-!
# The concrete CF3 site model: generator property and site-level expansions
-/

namespace FunctionalCapacity

noncomputable section
open Finset

/-- standing hypotheses on the operating parameters -/
structure Par.Valid (p : Par) : Prop where
  hM : 2 ≤ p.M
  hN : 0 < p.N
  hα : 0 ≤ p.α
  hβ : 0 ≤ p.β
  hε : 0 ≤ p.ε

namespace Site

variable {c N : ℕ}

theorem a_le (s : Site c N) (j : Fin c) : ((s.a j : ℕ) : ℝ) ≤ N := by
  exact_mod_cast Nat.lt_succ_iff.mp (s.a j).isLt

theorem a_nonneg (s : Site c N) (j : Fin c) : (0 : ℝ) ≤ ((s.a j : ℕ) : ℝ) := Nat.cast_nonneg _

theorem u_nonneg (s : Site c N) (j : Fin c) : 0 ≤ s.u j :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem u_le_one (s : Site c N) (j : Fin c) : s.u j ≤ 1 :=
  div_le_one_of_le₀ (a_le s j) (Nat.cast_nonneg _)

theorem r_nonneg (s : Site c N) : 0 ≤ s.r := by
  unfold r; split_ifs <;> norm_num

theorem r_le_one (s : Site c N) : s.r ≤ 1 := by
  unfold r; split_ifs <;> norm_num

theorem r_sq (s : Site c N) : s.r * s.r = s.r := by
  unfold r; split_ifs <;> norm_num

theorem a_eq_u_mul (hN : 0 < N) (s : Site c N) (j : Fin c) :
    ((s.a j : ℕ) : ℝ) = s.u j * N := by
  have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold u
  field_simp

theorem a_three_halves_nonneg (s : Site c N) (j : Fin c) :
    0 ≤ ((s.a j : ℕ) : ℝ) * (3 / 2 - s.u j) :=
  mul_nonneg (a_nonneg s j) (by linarith [u_le_one s j])

theorem a_three_halves_le (hN : 0 < N) (s : Site c N) (j : Fin c) :
    ((s.a j : ℕ) : ℝ) * (3 / 2 - s.u j) ≤ N * (9 / 16) := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  rw [a_eq_u_mul hN s j]
  nlinarith [mul_nonneg hN0 (sq_nonneg (s.u j - 3 / 4))]

end Site

/-! ### Elementary sum lemmas -/

theorem sum_split {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) (g : ι → ℝ) :
    ∑ v, g v = g i + ∑ v, if v = i then 0 else g v := by
  rw [sum_ite_ne_zero]; ring

theorem victim_avg {M : ℕ} (hM : 2 ≤ M) (i : Fin M) (A : ℝ) (g : Fin M → ℝ) :
    (1 / ((M : ℝ) - 1)) * (∑ v, if v = i then 0 else (A - g v))
      = A - (1 / ((M : ℝ) - 1)) * ∑ v, if v = i then 0 else g v := by
  have h : ∀ v, (if v = i then (0 : ℝ) else (A - g v))
      = (if v = i then 0 else A) - (if v = i then 0 else g v) := by
    intro v; split_ifs <;> simp
  have h2 := sum_victim_const hM i A
  simp_rw [h, Finset.sum_sub_distrib, mul_sub]
  rw [Finset.mul_sum]
  have h3 : ∀ v, (1 / ((M : ℝ) - 1)) * (if v = i then (0 : ℝ) else A)
      = if v = i then 0 else (1 / ((M : ℝ) - 1)) * A := by
    intro v; split_ifs <;> simp
  simp_rw [h3, h2]

theorem sum_victim_avg {M : ℕ} (hM : 2 ≤ M) (g : Fin M → ℝ) :
    ∑ i, (1 / ((M : ℝ) - 1)) * (∑ v, if v = i then 0 else g v) = ∑ v, g v := by
  have h0 := cast_sub_one_pos hM
  simp_rw [sum_ite_ne_zero, mul_sub, Finset.sum_sub_distrib]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  field_simp

/-! ### Binomial halving -/

theorem fin_sum_choose (N a : ℕ) (ha : a ≤ N) (g : ℕ → ℝ) :
    ∑ k : Fin (N + 1), ((a.choose k : ℕ) : ℝ) / 2 ^ a * g k = binE g a := by
  unfold binE
  rw [Fin.sum_univ_eq_sum_range (fun k => ((a.choose k : ℕ) : ℝ) / 2 ^ a * g k) (N + 1)]
  symm
  refine Finset.sum_subset (fun k hk => by simp only [Finset.mem_range] at *; omega) ?_
  intro k _ hk
  simp only [Finset.mem_range, not_lt] at hk
  rw [Nat.choose_eq_zero_of_lt (by omega)]
  simp

theorem binE_one (a : ℕ) : binE (fun _ => 1) a = 1 := by
  unfold binE
  simp only [mul_one]
  rw [← Finset.sum_div, ← Nat.cast_sum, Nat.sum_range_choose]
  push_cast
  exact div_self (by positivity)

theorem binE_add (f g : ℕ → ℝ) (a : ℕ) :
    binE (fun k => f k + g k) a = binE f a + binE g a := by
  unfold binE
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem binE_reflect (g : ℕ → ℝ) (a : ℕ) : binE (fun k => g (a - k)) a = binE g a := by
  unfold binE
  rw [← Finset.sum_range_reflect (fun k => ((a.choose k : ℕ) : ℝ) / 2 ^ a * g k) (a + 1)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  simp only [Nat.add_sub_cancel]
  rw [Nat.choose_symm hk']

theorem binE_half (f g : ℕ → ℝ) (a : ℕ) :
    binE (fun k => (f k + g k) / 2) a = (binE f a + binE g a) / 2 := by
  unfold binE
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem prod_marginal {c n : ℕ} (w : Fin c → Fin n → ℝ) (hw : ∀ j, ∑ k, w j k = 1)
    (j : Fin c) (h : Fin n → ℝ) :
    ∑ f : Fin c → Fin n, (∏ j', w j' (f j')) * h (f j) = ∑ k, w j k * h k := by
  have h1 : ∀ f : Fin c → Fin n, (∏ j', w j' (f j')) * h (f j)
      = ∏ j', (w j' (f j') * if j' = j then h (f j') else 1) := by
    intro f
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']
    simp
  refine ((Finset.sum_congr rfl fun f _ => h1 f).trans
    (Fintype.prod_sum (fun (j' : Fin c) (k : Fin n) =>
      w j' k * if j' = j then h k else 1)).symm).trans ?_
  have h2 : ∀ j', ∑ k, (w j' k * if j' = j then h k else 1)
      = if j' = j then ∑ k, w j k * h k else 1 := by
    intro j'
    split_ifs with e
    · subst e; rfl
    · simp [hw]
  simp_rw [h2]
  rw [Finset.prod_ite_eq']
  simp

/-! ### The CF3 fields -/

variable {p : Par}

/-- binomial allocation weight of species `j` -/
def wch (p : Par) (s : Site p.c p.N) (j : Fin p.c) (k : Fin (p.N + 1)) : ℝ :=
  ((Nat.choose (s.a j) k : ℕ) : ℝ) / 2 ^ (s.a j : ℕ)

theorem wch_nonneg (s : Site p.c p.N) (j : Fin p.c) (k : Fin (p.N + 1)) : 0 ≤ wch p s j k := by
  unfold wch; positivity

theorem wch_sum (s : Site p.c p.N) (j : Fin p.c) : ∑ k, wch p s j k = 1 := by
  have h := fin_sum_choose p.N (s.a j) (Nat.lt_succ_iff.mp (s.a j).isLt) (fun _ => 1)
  rw [binE_one] at h
  simpa [wch] using h

theorem wch_eq_zero (s : Site p.c p.N) (j : Fin p.c) (k : Fin (p.N + 1))
    (h : (s.a j : ℕ) < k) : wch p s j k = 0 := by
  unfold wch
  rw [Nat.choose_eq_zero_of_lt h]
  simp

theorem cf3_ps (s : Site p.c p.N) (o : Split p.c p.N) :
    (cf3 p).ps s o = (∏ j, wch p s j (o.1 j)) * (1 / 2) := rfl

theorem cf3_ps_nonneg (s : Site p.c p.N) (o : Split p.c p.N) : 0 ≤ (cf3 p).ps s o := by
  rw [cf3_ps]
  exact mul_nonneg (Finset.prod_nonneg fun j _ => wch_nonneg s j _) (by norm_num)

/-- the split weights are a probability distribution -/
theorem cf3_ps_sum (s : Site p.c p.N) : ∑ o, (cf3 p).ps s o = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, cf3_ps]
  have h : ∀ f : Fin p.c → Fin (p.N + 1),
      (∏ j, wch p s j (f j)) * (1 / 2) + (∏ j, wch p s j (f j)) * (1 / 2)
        = ∏ j, wch p s j (f j) := fun f => by ring
  refine ((Finset.sum_congr rfl fun f _ => h f).trans
    (Fintype.prod_sum (fun (j : Fin p.c) (k : Fin (p.N + 1)) => wch p s j k)).symm).trans ?_
  simp [wch_sum]

/-- a split outcome of positive weight allocates at most the available molecules -/
theorem cf3_ps_support (s : Site p.c p.N) (o : Split p.c p.N) (h : (cf3 p).ps s o ≠ 0)
    (j : Fin p.c) : ((o.1 j : Fin (p.N + 1)) : ℕ) ≤ (s.a j : ℕ) := by
  by_contra hlt
  apply h
  rw [cf3_ps, Finset.prod_eq_zero (Finset.mem_univ j) (wch_eq_zero s j _ (not_le.mp hlt)),
    zero_mul]

/-- marginal of the split on one species and the fuel coin -/
theorem cf3_ps_marg (s : Site p.c p.N) (j : Fin p.c) (h : ℕ → Bool → ℝ) :
    ∑ o, (cf3 p).ps s o * h (o.1 j) o.2
      = (binE (fun k => h k true) (s.a j) + binE (fun k => h k false) (s.a j)) / 2 := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, cf3_ps]
  have h1 : ∀ f : Fin p.c → Fin (p.N + 1),
      (∏ j', wch p s j' (f j')) * (1 / 2) * h (f j) true
        + (∏ j', wch p s j' (f j')) * (1 / 2) * h (f j) false
        = (∏ j', wch p s j' (f j')) *
          ((fun k : Fin (p.N + 1) => (h k true + h k false) / 2) (f j)) := fun f => by
    simp only; ring
  rw [Finset.sum_congr rfl fun f _ => h1 f,
    prod_marginal (fun j' k => wch p s j' k) (fun j' => wch_sum s j') j
      (fun k : Fin (p.N + 1) => (h k true + h k false) / 2), ← binE_half]
  exact fin_sum_choose p.N (s.a j) (Nat.lt_succ_iff.mp (s.a j).isLt)
    (fun k => (h k true + h k false) / 2)

/-- expansion of the within-site channel sum -/
theorem cf3_chem_sum (p : Par) (s : Site p.c p.N) (F : Site p.c p.N → ℝ) :
    ∑ k, (cf3 p).rc s k * F ((cf3 p).tc s k) =
      (∑ j, p.ε * (1 - s.u j) *
          F { s with a := Function.update s.a j (Site.inc (s.a j)) })
      + (∑ j, p.α * s.r * ((s.a j : ℕ) : ℝ) * (1 - s.u j) *
          F { s with a := Function.update s.a j (Site.inc (s.a j)), R := false })
      + (∑ j, p.α / 2 * s.r * ((s.a j : ℕ) : ℝ) *
          F { s with a := Function.update s.a j (Site.dec (s.a j)), R := false })
      + (∑ j, ((s.a j : ℕ) : ℝ) *
          F { s with a := Function.update s.a j (Site.dec (s.a j)) })
      + (∑ j, p.β * s.u j * s.r *
          F { s with R := false, q := Function.update s.q j (s.q j + 1) })
      + (p.β * s.r * F { s with R := false } + p.β * (1 - s.r) * F { s with R := true }) := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_five, Fintype.sum_bool]
  rfl

/-- expansion of the division channel sum -/
theorem cf3_div_sum (p : Par) (s : Site p.c p.N) (G : Site p.c p.N → ℝ) :
    ∑ k, (cf3 p).rd s k * G ((cf3 p).td s k) =
      G { s with nd := s.nd + 1 }
      + ∑ j, s.u j * s.r *
          G { s with R := false, q := Function.update s.q j (s.q j + 1), nd := s.nd + 1 } := by
  rw [Fintype.sum_option]
  exact congrArg₂ _ (one_mul _) rfl

/-! ### B1: the CF3 population generator is a bounded generator -/

theorem cf3_rc_nonneg (hp : p.Valid) (s : Site p.c p.N) (k : Chem p.c) : 0 ≤ (cf3 p).rc s k := by
  have hr0 := s.r_nonneg
  have hr1 := s.r_le_one
  rcases k with ⟨t, j⟩ | b
  · have h1u : 0 ≤ 1 - s.u j := by linarith [s.u_le_one j]
    have hu0 := s.u_nonneg j
    have ha0 := s.a_nonneg j
    show 0 ≤ (if t = 0 then p.ε * (1 - s.u j)
        else if t = 1 then p.α * s.r * ((s.a j : ℕ) : ℝ) * (1 - s.u j)
        else if t = 2 then p.α / 2 * s.r * ((s.a j : ℕ) : ℝ)
        else if t = 3 then ((s.a j : ℕ) : ℝ)
        else p.β * s.u j * s.r)
    split_ifs
    · exact mul_nonneg hp.hε h1u
    · exact mul_nonneg (mul_nonneg (mul_nonneg hp.hα hr0) ha0) h1u
    · exact mul_nonneg (mul_nonneg (by linarith [hp.hα]) hr0) ha0
    · exact ha0
    · exact mul_nonneg (mul_nonneg hp.hβ hu0) hr0
  · cases b
    · exact mul_nonneg hp.hβ (by linarith)
    · exact mul_nonneg hp.hβ hr0

theorem cf3_rd_nonneg (s : Site p.c p.N) (k : Option (Fin p.c)) : 0 ≤ (cf3 p).rd s k := by
  cases k with
  | none => exact zero_le_one
  | some j => exact mul_nonneg (s.u_nonneg j) s.r_nonneg

theorem cf3_rc_sum_le (hp : p.Valid) (s : Site p.c p.N) :
    ∑ k, (cf3 p).rc s k
      ≤ p.c * (p.ε + p.α * p.N + p.α / 2 * p.N + p.N + p.β) + p.β := by
  have h := cf3_chem_sum p s (fun _ => 1)
  simp only [mul_one] at h
  rw [h, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  have hr0 := s.r_nonneg
  have hr1 := s.r_le_one
  have hN0 : (0 : ℝ) ≤ p.N := Nat.cast_nonneg _
  have key : ∀ j : Fin p.c, p.ε * (1 - s.u j) + p.α * s.r * ((s.a j : ℕ) : ℝ) * (1 - s.u j)
      + p.α / 2 * s.r * ((s.a j : ℕ) : ℝ) + ((s.a j : ℕ) : ℝ) + p.β * s.u j * s.r
      ≤ p.ε + p.α * p.N + p.α / 2 * p.N + p.N + p.β := by
    intro j
    have h1u : 0 ≤ 1 - s.u j := by linarith [s.u_le_one j]
    have hu0 := s.u_nonneg j
    have hu1 := s.u_le_one j
    have ha0 := s.a_nonneg j
    have haN := s.a_le j
    have t1 : s.r * ((s.a j : ℕ) : ℝ) ≤ 1 * p.N := mul_le_mul hr1 haN ha0 zero_le_one
    have t2 : s.r * ((s.a j : ℕ) : ℝ) * (1 - s.u j) ≤ 1 * p.N * 1 :=
      mul_le_mul t1 (by linarith) h1u (by linarith)
    have t3 : s.u j * s.r ≤ 1 * 1 := mul_le_mul hu1 hr1 hr0 zero_le_one
    have e1 := mul_le_mul_of_nonneg_left (show 1 - s.u j ≤ 1 by linarith) hp.hε
    have e2 := mul_le_mul_of_nonneg_left t2 hp.hα
    have e3 := mul_le_mul_of_nonneg_left t1 hp.hα
    have e5 := mul_le_mul_of_nonneg_left t3 hp.hβ
    linarith
  have hs := Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin p.c))) => key j
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have : p.β * s.r + p.β * (1 - s.r) = p.β := by ring
  linarith

theorem cf3_rd_sum_le (s : Site p.c p.N) : ∑ k, (cf3 p).rd s k ≤ 1 + p.c := by
  have h := cf3_div_sum p s (fun _ => 1)
  simp only [mul_one] at h
  rw [h]
  have hs : ∑ j, s.u j * s.r ≤ ∑ _j : Fin p.c, (1 : ℝ) :=
    Finset.sum_le_sum fun j _ => by
      have := mul_le_mul (s.u_le_one j) s.r_le_one s.r_nonneg zero_le_one
      linarith
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hs
  linarith

/-- B1 -/
theorem cf3_isGen (hp : p.Valid) : IsGen (cf3Rate p) (cf3Gen p) :=
  popGen_isGen (cf3 p) p.M hp.hM (cf3_rc_nonneg hp) cf3_rd_nonneg cf3_ps_nonneg
    (cf3_rc_sum_le hp) cf3_rd_sum_le (fun s => (cf3_ps_sum s).le)

end

end FunctionalCapacity

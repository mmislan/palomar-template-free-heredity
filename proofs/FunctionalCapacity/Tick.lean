module

public import proofs.FunctionalCapacity.Kernel

@[expose] public section

/-!
# From generator inequalities to tick inequalities, and the block induction

* `tick_super` : `G V ≤ -θ V + b` on live states gives `P V ≤ (1 - θ/Λ) V + b/Λ` for the killed tick.
* `tick_sub`   : if `Φ ≥ 1` on the killed set and `G Φ ≤ b` on live states, then `1 - Φ` loses at
                 most `b/Λ` per tick (killing included).
* `blocks_lower` : lower bound for a mission of `n` blocks with a guard potential `Φ`, a decaying
                 potential `V`, and service potentials `Y k` certifying the end-of-block requirement.
-/

namespace FunctionalCapacity

noncomputable section
open Finset

variable {σ : Type}

theorem tick_super {L Lam : ℝ} {G : (σ → ℝ) → σ → ℝ} (hG : IsGen L G) (hLam : 0 < Lam)
    (hL : L ≤ Lam) (dead : σ → Prop) [DecidablePred dead] {V : σ → ℝ} {θ b : ℝ}
    (hV : ∀ y, 0 ≤ V y) (hθ : θ ≤ Lam) (hb : 0 ≤ b)
    (h : ∀ x, ¬ dead x → G V x ≤ -θ * V x + b) (x : σ) :
    (killed hG hLam hL dead).P V x ≤ (1 - θ / Lam) * V x + b / Lam := by
  rw [killed_P]
  unfold stepK
  by_cases hd : dead x
  · rw [ite_eq_left hd]
    have h1 : 0 ≤ 1 - θ / Lam := by
      have : θ / Lam ≤ 1 := (div_le_one hLam).2 hθ
      linarith
    have h2 : 0 ≤ b / Lam := div_nonneg hb hLam.le
    have := mul_nonneg h1 (hV x)
    linarith
  · rw [ite_eq_right hd]
    have hk : ∀ y, 0 ≤ V y - kill dead V y := by
      intro y
      unfold kill
      split_ifs
      · simpa using hV y
      · simp
    have hp := hG.pos (fun y => V y - kill dead V y) hk x
    rw [hG.sub] at hp
    have hx : kill dead V x = V x := by unfold kill; rw [ite_eq_right hd]
    rw [hx] at hp
    have hle : G (kill dead V) x ≤ -θ * V x + b := by
      have := h x hd
      simp only [sub_self, mul_zero, zero_add] at hp
      linarith
    have hdiv : G (kill dead V) x / Lam ≤ (-θ * V x + b) / Lam :=
      div_le_div_of_nonneg_right hle hLam.le
    have e : (-θ * V x + b) / Lam = -(θ / Lam) * V x + b / Lam := by ring
    rw [e] at hdiv
    linarith

theorem tick_sub {L Lam : ℝ} {G : (σ → ℝ) → σ → ℝ} (hG : IsGen L G) (hLam : 0 < Lam)
    (hL : L ≤ Lam) (dead : σ → Prop) [DecidablePred dead] {Φ : σ → ℝ} {b : ℝ}
    (hb : 0 ≤ b) (hdead : ∀ y, dead y → 1 ≤ Φ y)
    (h : ∀ x, ¬ dead x → G Φ x ≤ b) (x : σ) :
    (1 - Φ x) - b / Lam ≤ (killed hG hLam hL dead).P (fun y => 1 - Φ y) x := by
  rw [killed_P]
  unfold stepK
  have h2 : 0 ≤ b / Lam := div_nonneg hb hLam.le
  by_cases hd : dead x
  · rw [ite_eq_left hd]
    have := hdead x hd
    linarith
  · rw [ite_eq_right hd]
    have hk : ∀ y, 0 ≤ kill dead (fun y => 1 - Φ y) y - (1 - Φ y) := by
      intro y
      unfold kill
      split_ifs with hy
      · have := hdead y hy
        linarith
      · simp
    have hp := hG.pos (fun y => kill dead (fun y => 1 - Φ y) y - (1 - Φ y)) hk x
    rw [hG.sub] at hp
    have hx : kill dead (fun y => 1 - Φ y) x = 1 - Φ x := by unfold kill; rw [ite_eq_right hd]
    rw [hx] at hp
    have hg : G (fun y => 1 - Φ y) x = -G Φ x := by
      rw [hG.sub (fun _ => 1) Φ x, hG.one]; ring
    rw [hg] at hp
    have hΦ := h x hd
    have hge : -b ≤ G (kill dead (fun y => 1 - Φ y)) x := by
      simp only [sub_self, mul_zero, zero_add] at hp
      linarith
    have hdiv : -b / Lam ≤ G (kill dead (fun y => 1 - Φ y)) x / Lam :=
      div_le_div_of_nonneg_right hge hLam.le
    have e : -b / Lam = -(b / Lam) := by ring
    rw [e] at hdiv
    linarith

theorem blocks_bdd (K : SubMarkov σ) {μ : ℝ} (hμ : 0 ≤ μ) (ok : σ → Prop) [DecidablePred ok]
    (reset : σ → σ) {F : σ → ℝ} (hF : Bdd F) (n : ℕ) : Bdd (blocks K μ ok reset n F) := by
  induction n with
  | zero => exact hF
  | succ n ih =>
    obtain ⟨B, hB⟩ := Bdd.blockArg (ok := ok) (reset := reset) ih
    exact ⟨B, fun x => K.ct_abs_le hμ hB x⟩

/-- Mission lower bound for `n` blocks. -/
theorem blocks_lower (K : SubMarkov σ) {μ : ℝ} (hμ : 0 ≤ μ) (ok : σ → Prop) [DecidablePred ok]
    (reset : σ → σ) {ι : Type} (s : Finset ι) (Y : ι → σ → ℝ)
    {Φ V F : σ → ℝ} {BΦ BV bΦ bV θV θs cV A E0 : ℝ}
    (hΦ0 : ∀ y, 0 ≤ Φ y) (hΦB : ∀ y, Φ y ≤ BΦ) (hΦr : ∀ y, Φ (reset y) = Φ y)
    (hbΦ : 0 ≤ bΦ) (hΦsub : ∀ x, (1 - Φ x) - bΦ ≤ K.P (fun y => 1 - Φ y) x)
    (hV0 : ∀ y, 0 ≤ V y) (hVB : ∀ y, V y ≤ BV) (hVr : ∀ y, V (reset y) = V y)
    (hθV0 : 0 ≤ θV) (hθV1 : θV ≤ 1) (hbV : 0 ≤ bV)
    (hVsup : ∀ x, K.P V x ≤ (1 - θV) * V x + bV)
    (hY0 : ∀ k ∈ s, ∀ y, 0 ≤ Y k y) (hY1 : ∀ k ∈ s, ∀ y, Y k y ≤ 1)
    (hθs0 : 0 ≤ θs) (hθs1 : θs ≤ 1)
    (hYsup : ∀ k ∈ s, ∀ x, K.P (Y k) x ≤ (1 - θs) * Y k x)
    (hA : 0 ≤ A) (hok : ∀ y, ¬ ok y → ∃ k ∈ s, 1 ≤ A * Y k y)
    (hcV : 0 ≤ cV) (hE0 : 0 ≤ E0) (hFB : Bdd F)
    (hF : ∀ x, 1 - Φ x - cV * V x - E0 ≤ F x) (n : ℕ) (x : σ) :
    1 - Φ x - cV * (Real.exp (-(θV * μ * n)) * V x) - E0
        - n * (bΦ * μ + cV * (bV * μ) + A * (s.card * Real.exp (-(θs * μ))))
      ≤ blocks K μ ok reset n F x := by
  induction n generalizing x with
  | zero =>
    simp only [blocks, Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, one_mul, zero_mul,
      sub_zero]
    exact hF x
  | succ n ih =>
    set δ : ℝ := bΦ * μ + cV * (bV * μ) + A * (s.card * Real.exp (-(θs * μ))) with hδ
    have hδ0 : 0 ≤ δ := by
      have h1 : 0 ≤ bΦ * μ := mul_nonneg hbΦ hμ
      have h2 : 0 ≤ cV * (bV * μ) := mul_nonneg hcV (mul_nonneg hbV hμ)
      have h3 : 0 ≤ A * (s.card * Real.exp (-(θs * μ))) :=
        mul_nonneg hA (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)
      linarith
    set e : ℝ := Real.exp (-(θV * μ * n)) with he
    have he0 : 0 ≤ e := (Real.exp_pos _).le
    have he1 : e ≤ 1 := by
      rw [he]; apply Real.exp_le_one_iff.2
      have : 0 ≤ θV * μ * n := mul_nonneg (mul_nonneg hθV0 hμ) (Nat.cast_nonneg _)
      linarith
    -- pointwise lower bound of the block integrand
    set lowf : σ → ℝ := fun y =>
      (1 - Φ y) - (cV * e) * V y - (E0 + n * δ) - A * ∑ k ∈ s, Y k y with hlow
    have hsumY0 : ∀ y, 0 ≤ ∑ k ∈ s, Y k y := fun y => Finset.sum_nonneg (fun k hk => hY0 k hk y)
    have hpt : ∀ y, lowf y ≤ (if ok y then blocks K μ ok reset n F (reset y) else 0) := by
      intro y
      have hce : 0 ≤ cV * e * V y := mul_nonneg (mul_nonneg hcV he0) (hV0 y)
      have hnδ : 0 ≤ (n : ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) hδ0
      have hAY : 0 ≤ A * ∑ k ∈ s, Y k y := mul_nonneg hA (hsumY0 y)
      by_cases hy : ok y
      · rw [ite_eq_left hy]
        have := ih (reset y)
        rw [hΦr, hVr] at this
        simp only [hlow]
        have e2 : cV * (e * V y) = cV * e * V y := by ring
        rw [e2] at this
        linarith
      · rw [ite_eq_right hy]
        obtain ⟨k, hk, hk1⟩ := hok y hy
        have hle : Y k y ≤ ∑ k ∈ s, Y k y :=
          Finset.single_le_sum (fun k hk => hY0 k hk y) hk
        have : 1 ≤ A * ∑ k ∈ s, Y k y := le_trans hk1 (mul_le_mul_of_nonneg_left hle hA)
        simp only [hlow]
        have := hΦ0 y
        linarith
    -- boundedness
    have hBΦ : Bdd (fun y => 1 - Φ y) := (Bdd.const 1).sub (Bdd.of_le hΦ0 hΦB)
    have hBV : Bdd V := Bdd.of_le hV0 hVB
    have hBY : ∀ k ∈ s, Bdd (Y k) := fun k hk => Bdd.of_le (hY0 k hk) (hY1 k hk)
    have hBsum : Bdd (fun y => ∑ k ∈ s, Y k y) := Bdd.sum s Y hBY
    have hB1 : Bdd (fun y => (1 - Φ y) - (cV * e) * V y) := hBΦ.sub (hBV.smul _)
    have hB2 : Bdd (fun y => (1 - Φ y) - (cV * e) * V y - (E0 + n * δ)) := hB1.sub (Bdd.const _)
    have hBlow : Bdd lowf := hB2.sub (hBsum.smul A)
    have hBarg : Bdd (fun y => if ok y then blocks K μ ok reset n F (reset y) else 0) :=
      Bdd.blockArg (blocks_bdd K hμ ok reset hFB n)
    have hmono := K.ct_mono hμ hBlow hBarg hpt x
    -- evaluate ct of the lower function
    have hct : K.ct μ lowf x =
        K.ct μ (fun y => 1 - Φ y) x - (cV * e) * K.ct μ V x
          - K.ct μ (fun _ => E0 + n * δ) x - A * ∑ k ∈ s, K.ct μ (Y k) x := by
      simp only [hlow]
      rw [K.ct_sub hB2 (hBsum.smul A), K.ct_sub hB1 (Bdd.const _), K.ct_sub hBΦ (hBV.smul _),
        K.ct_smul, K.ct_smul, K.ct_sum s Y hBY]
    have h1 : (1 - Φ x) - bΦ * μ ≤ K.ct μ (fun y => 1 - Φ y) x := by
      obtain ⟨B, hB⟩ := hBΦ
      exact K.ct_sub_lower hB hbΦ hμ hΦsub x
    have h2 : K.ct μ V x ≤ Real.exp (-(θV * μ)) * V x + bV * μ :=
      K.ct_super hV0 hVB hθV0 hθV1 hbV hμ hVsup x
    have h3 : K.ct μ (fun _ => E0 + n * δ) x ≤ E0 + n * δ := by
      have hc : 0 ≤ E0 + n * δ := add_nonneg hE0 (mul_nonneg (Nat.cast_nonneg _) hδ0)
      exact K.ct_le hμ hc (fun _ => hc) (fun _ => le_refl _) x
    have h4 : ∑ k ∈ s, K.ct μ (Y k) x ≤ s.card * Real.exp (-(θs * μ)) := by
      have : ∀ k ∈ s, K.ct μ (Y k) x ≤ Real.exp (-(θs * μ)) := by
        intro k hk
        have hs := K.ct_super (b := 0) (hY0 k hk) (hY1 k hk) hθs0 hθs1 (le_refl 0) hμ
          (fun x => by simpa using hYsup k hk x) x
        have hexp : 0 ≤ Real.exp (-(θs * μ)) := (Real.exp_pos _).le
        have := mul_le_mul_of_nonneg_left (hY1 k hk x) hexp
        linarith
      calc ∑ k ∈ s, K.ct μ (Y k) x ≤ ∑ _k ∈ s, Real.exp (-(θs * μ)) := Finset.sum_le_sum this
        _ = s.card * Real.exp (-(θs * μ)) := by simp
    have hexp : Real.exp (-(θV * μ * (n + 1 : ℕ))) = e * Real.exp (-(θV * μ)) := by
      rw [he, ← Real.exp_add]; congr 1; push_cast; ring
    have hce : 0 ≤ cV * e := mul_nonneg hcV he0
    have h2' := mul_le_mul_of_nonneg_left h2 hce
    have h4' := mul_le_mul_of_nonneg_left h4 hA
    have hbVμ : 0 ≤ bV * μ := mul_nonneg hbV hμ
    have h5 : cV * e * (bV * μ) ≤ cV * (bV * μ) := by
      have := mul_le_mul_of_nonneg_right he1 (mul_nonneg hcV hbVμ)
      nlinarith [this]
    show _ ≤ block K μ ok reset (blocks K μ ok reset n F) x
    unfold block
    rw [hexp]
    push_cast
    rw [hct] at hmono
    have e3 : cV * (e * Real.exp (-(θV * μ)) * V x) = cV * e * (Real.exp (-(θV * μ)) * V x) := by
      ring
    rw [e3]
    have e4 : cV * e * (Real.exp (-(θV * μ)) * V x + bV * μ)
        = cV * e * (Real.exp (-(θV * μ)) * V x) + cV * e * (bV * μ) := by ring
    rw [e4] at h2'
    linarith

end

end FunctionalCapacity

#print axioms FunctionalCapacity.blocks_lower
#print axioms FunctionalCapacity.blocks_bdd

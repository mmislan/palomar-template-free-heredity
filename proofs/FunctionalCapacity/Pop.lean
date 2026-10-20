module

public import proofs.FunctionalCapacity.Defs

@[expose] public section

/-!
# Generic lemmas on the population generator `popGen`

* `popGen_isGen`    : `popGen` is a bounded generator.
* `popGen_single`   : action on a function of one site.
* `popGen_additive` : action on an additive function `∑ i, y (z i)`.
-/

namespace FunctionalCapacity

noncomputable section
open Finset

variable {S ιc ιd ιs : Type} [Fintype ιc] [Fintype ιd] [Fintype ιs]

theorem sum_ite_ne_zero {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) (g : ι → ℝ) :
    (∑ v, if v = i then 0 else g v) = (∑ v, g v) - g i := by
  have h : ∀ v, (if v = i then 0 else g v) = g v - if v = i then g v else 0 := by
    intro v; split_ifs <;> simp
  simp_rw [h, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem cast_sub_one_pos {M : ℕ} (hM : 2 ≤ M) : (0 : ℝ) < (M : ℝ) - 1 := by
  have : (2 : ℝ) ≤ M := by exact_mod_cast hM
  linarith

/-- the `M - 1` possible victims carry total weight one -/
theorem sum_victim_const {M : ℕ} (hM : 2 ≤ M) (i : Fin M) (c : ℝ) :
    (∑ v : Fin M, if v = i then 0 else (1 / ((M : ℝ) - 1)) * c) = c := by
  rw [sum_ite_ne_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h0 := cast_sub_one_pos hM
  have h : (M : ℝ) * (1 / ((M : ℝ) - 1) * c) - 1 / ((M : ℝ) - 1) * c
      = (((M : ℝ) - 1) * (1 / ((M : ℝ) - 1))) * c := by ring
  rw [h, mul_one_div_cancel h0.ne', one_mul]

theorem sum_update_apply {M : ℕ} (y : S → ℝ) (x : Fin M → S) (i : Fin M) (s : S) :
    ∑ j, y (Function.update x i s j) = (∑ j, y (x j)) + (y s - y (x i)) := by
  have h : ∀ j, y (Function.update x i s j) = y (x j) + if j = i then y s - y (x i) else 0 := by
    intro j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  simp_rw [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- contribution of the events initiated at site `i` -/
def siteTerm (m : SiteModel S ιc ιd ιs) (M : ℕ) (f : (Fin M → S) → ℝ) (x : Fin M → S)
    (i : Fin M) : ℝ :=
  (∑ k, m.rc (x i) k * (f (Function.update x i (m.tc (x i) k)) - f x))
    + ∑ k, m.rd (x i) k * ∑ o, m.ps (m.td (x i) k) o *
        ∑ v, if v = i then 0 else
          (1 / ((M : ℝ) - 1)) *
            (f (Function.update (Function.update x i (m.d1 (m.td (x i) k) o)) v
                (m.merge (x v) (m.d2 (m.td (x i) k) o))) - f x)

theorem popGen_eq (m : SiteModel S ιc ιd ιs) (M : ℕ) (f : (Fin M → S) → ℝ) (x : Fin M → S) :
    popGen m M f x = ∑ i, siteTerm m M f x i := rfl

theorem popGen_add (m : SiteModel S ιc ιd ιs) (M : ℕ) (f g : (Fin M → S) → ℝ) (x : Fin M → S) :
    popGen m M (fun y => f y + g y) x = popGen m M f x + popGen m M g x := by
  simp only [popGen]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_add_add_comm, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun k _ => by ring
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs <;> ring

theorem popGen_smul (m : SiteModel S ιc ιd ιs) (M : ℕ) (c : ℝ) (f : (Fin M → S) → ℝ)
    (x : Fin M → S) :
    popGen m M (fun y => c * f y) x = c * popGen m M f x := by
  simp only [popGen]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun k _ => by ring
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_left_comm]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [mul_left_comm]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs <;> ring

/-- A1: the population generator is a bounded generator. -/
theorem popGen_isGen (m : SiteModel S ιc ιd ιs) (M : ℕ) (hM : 2 ≤ M) {Lc Ld : ℝ}
    (hrc : ∀ s k, 0 ≤ m.rc s k) (hrd : ∀ s k, 0 ≤ m.rd s k) (hps : ∀ s o, 0 ≤ m.ps s o)
    (hLc : ∀ s, ∑ k, m.rc s k ≤ Lc) (hLd : ∀ s, ∑ k, m.rd s k ≤ Ld)
    (hps1 : ∀ s, ∑ o, m.ps s o ≤ 1) :
    IsGen ((M : ℝ) * (Lc + Ld)) (popGen m M) := by
  have hM1 := cast_sub_one_pos hM
  refine ⟨popGen_add m M, popGen_smul m M, fun x => by simp [popGen], ?_⟩
  intro f hf x
  have key : ∑ _i : Fin M, (-(Lc + Ld) * f x) ≤ popGen m M f x := by
    unfold popGen
    refine Finset.sum_le_sum fun i _ => ?_
    rw [show -(Lc + Ld) * f x = -Lc * f x + -Ld * f x by ring]
    refine add_le_add ?_ ?_
    · calc -Lc * f x ≤ (∑ k, m.rc (x i) k) * (-f x) := by nlinarith [hLc (x i), hf x]
        _ = ∑ k, m.rc (x i) k * (-f x) := Finset.sum_mul _ _ _
        _ ≤ _ := Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_left (by linarith [hf (Function.update x i (m.tc (x i) k))])
              (hrc _ _)
    · have inner : ∀ k o, -f x ≤ ∑ v, if v = i then 0 else
          (1 / ((M : ℝ) - 1)) *
            (f (Function.update (Function.update x i (m.d1 (m.td (x i) k) o)) v
                (m.merge (x v) (m.d2 (m.td (x i) k) o))) - f x) := by
        intro k o
        calc -f x = ∑ v : Fin M, if v = i then 0 else (1 / ((M : ℝ) - 1)) * (-f x) :=
              (sum_victim_const hM i _).symm
          _ ≤ _ := Finset.sum_le_sum fun v _ => by
              split_ifs
              · exact le_rfl
              · exact mul_le_mul_of_nonneg_left (by linarith [hf (Function.update
                  (Function.update x i (m.d1 (m.td (x i) k) o)) v
                  (m.merge (x v) (m.d2 (m.td (x i) k) o)))]) (one_div_pos.mpr hM1).le
      have mid : ∀ k, -f x ≤ ∑ o, m.ps (m.td (x i) k) o * ∑ v, if v = i then 0 else
          (1 / ((M : ℝ) - 1)) *
            (f (Function.update (Function.update x i (m.d1 (m.td (x i) k) o)) v
                (m.merge (x v) (m.d2 (m.td (x i) k) o))) - f x) := by
        intro k
        calc -f x ≤ (∑ o, m.ps (m.td (x i) k) o) * (-f x) := by
              nlinarith [hps1 (m.td (x i) k), hf x]
          _ = ∑ o, m.ps (m.td (x i) k) o * (-f x) := Finset.sum_mul _ _ _
          _ ≤ _ := Finset.sum_le_sum fun o _ =>
              mul_le_mul_of_nonneg_left (inner k o) (hps _ _)
      calc -Ld * f x ≤ (∑ k, m.rd (x i) k) * (-f x) := by nlinarith [hLd (x i), hf x]
        _ = ∑ k, m.rd (x i) k * (-f x) := Finset.sum_mul _ _ _
        _ ≤ _ := Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (mid k) (hrd _ _)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at key
  nlinarith [key]

/-- A2: action of the population generator on a function of the single site `i0`. -/
theorem popGen_single (m : SiteModel S ιc ιd ιs) (M : ℕ) (hM : 2 ≤ M) (i0 : Fin M) (y : S → ℝ)
    (x : Fin M → S) :
    popGen m M (fun z => y (z i0)) x =
      (∑ k, m.rc (x i0) k * (y (m.tc (x i0) k) - y (x i0)))
      + (∑ k, m.rd (x i0) k * ∑ o, m.ps (m.td (x i0) k) o *
          (y (m.d1 (m.td (x i0) k) o) - y (x i0)))
      + ∑ i, if i = i0 then 0 else
          ∑ k, m.rd (x i) k * ∑ o, m.ps (m.td (x i) k) o *
            ((1 / ((M : ℝ) - 1)) * (y (m.merge (x i0) (m.d2 (m.td (x i) k) o)) - y (x i0))) := by
  have key : ∀ i : Fin M, siteTerm m M (fun z => y (z i0)) x i =
      (if i = i0 then
        (∑ k, m.rc (x i0) k * (y (m.tc (x i0) k) - y (x i0)))
        + (∑ k, m.rd (x i0) k * ∑ o, m.ps (m.td (x i0) k) o *
            (y (m.d1 (m.td (x i0) k) o) - y (x i0))) else 0)
      + (if i = i0 then 0 else
          ∑ k, m.rd (x i) k * ∑ o, m.ps (m.td (x i) k) o *
            ((1 / ((M : ℝ) - 1)) *
              (y (m.merge (x i0) (m.d2 (m.td (x i) k) o)) - y (x i0)))) := by
    intro i
    by_cases h : i = i0
    · subst h
      rw [ite_eq_left rfl, ite_eq_left rfl, add_zero]
      simp only [siteTerm]
      congr 1
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [Function.update_self]
      · refine Finset.sum_congr rfl fun k _ => ?_
        congr 1
        refine Finset.sum_congr rfl fun o _ => ?_
        congr 1
        refine Eq.trans ?_ (sum_victim_const hM i _)
        refine Finset.sum_congr rfl fun v _ => ?_
        split_ifs with hv
        · rfl
        · rw [Function.update_of_ne (Ne.symm hv), Function.update_self]
    · rw [ite_eq_right h, ite_eq_right h, zero_add]
      simp only [siteTerm]
      have c0 : ∀ k, m.rc (x i) k *
          (y (Function.update x i (m.tc (x i) k) i0) - y (x i0)) = 0 := fun k => by
        rw [Function.update_of_ne (Ne.symm h), sub_self, mul_zero]
      simp only [c0, Finset.sum_const_zero, zero_add]
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun o _ => ?_
      congr 1
      rw [Finset.sum_eq_single i0]
      · rw [ite_eq_right (Ne.symm h), Function.update_self]
      · intro v _ hv
        split_ifs
        · rfl
        · rw [Function.update_of_ne hv.symm, Function.update_of_ne (Ne.symm h), sub_self,
            mul_zero]
      · intro h'
        exact absurd (Finset.mem_univ _) h'
  rw [popGen_eq, Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib,
    Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]

/-- A3: action of the population generator on an additive function. -/
theorem popGen_additive (m : SiteModel S ιc ιd ιs) (M : ℕ) (hM : 2 ≤ M) (y : S → ℝ)
    (x : Fin M → S) :
    popGen m M (fun z => ∑ i, y (z i)) x =
      ∑ i, ((∑ k, m.rc (x i) k * (y (m.tc (x i) k) - y (x i)))
        + ∑ k, m.rd (x i) k * ∑ o, m.ps (m.td (x i) k) o *
            ((y (m.d1 (m.td (x i) k) o) - y (x i))
             + (1 / ((M : ℝ) - 1)) * ∑ v, if v = i then 0 else
                 (y (m.merge (x v) (m.d2 (m.td (x i) k) o)) - y (x v)))) := by
  simp only [popGen]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [sum_update_apply]
    ring
  · refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun o _ => ?_
    congr 1
    have hv : ∀ v : Fin M, (if v = i then (0 : ℝ) else (1 / ((M : ℝ) - 1)) *
          ((∑ j, y (Function.update (Function.update x i (m.d1 (m.td (x i) k) o)) v
              (m.merge (x v) (m.d2 (m.td (x i) k) o)) j)) - ∑ j, y (x j))) =
        (if v = i then 0 else (1 / ((M : ℝ) - 1)) * (y (m.d1 (m.td (x i) k) o) - y (x i)))
        + (1 / ((M : ℝ) - 1)) * (if v = i then 0 else
            (y (m.merge (x v) (m.d2 (m.td (x i) k) o)) - y (x v))) := by
      intro v
      split_ifs with h
      · simp
      · rw [sum_update_apply, sum_update_apply, Function.update_of_ne h]
        ring
    rw [Finset.sum_congr rfl fun v _ => hv v, Finset.sum_add_distrib, sum_victim_const hM,
      ← Finset.mul_sum]

end

end FunctionalCapacity

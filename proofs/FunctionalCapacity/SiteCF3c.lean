module

public import proofs.FunctionalCapacity.SiteCF3b

@[expose] public section

/-!
# CF3: single-site potentials (division ledger and service ledger)
-/

namespace FunctionalCapacity

noncomputable section
open Finset

variable {p : Par}

theorem sum_updG {c : ℕ} {α : Type} (a : Fin c → α) (j : Fin c) (cf : Fin c → ℝ)
    (v : Fin c → α) (G : α → ℝ) (c0 : ℝ) :
    ∑ j', cf j' * (G (Function.update a j' (v j') j) - c0)
      = cf j * (G (v j) - c0) + (∑ j', if j' = j then 0 else cf j') * (G (a j) - c0) := by
  rw [sum_split j (fun j' => cf j' * (G (Function.update a j' (v j') j) - c0)),
    Function.update_self, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun j' _ => ?_
  split_ifs with h
  · simp
  · rw [Function.update_of_ne (Ne.symm h)]

/-! ### B4: the division ledger -/

theorem cf3Gen_div (hp : p.Valid) (i0 : Fin p.M) (g : ℕ → ℝ) (hgm : ∀ n, g (n + 1) ≤ g n)
    (x : Fin p.M → Site p.c p.N) :
    cf3Gen p (fun z => g (z i0).nd) x ≤ -(g (x i0).nd - g ((x i0).nd + 1)) := by
  unfold cf3Gen
  refine le_of_eq_of_le (popGen_single (cf3 p) p.M hp.hM i0 (fun s => g s.nd) x) ?_
  have hc := cf3_chem_sum p (x i0) (fun s' => g s'.nd - g (x i0).nd)
  simp only [sub_self, mul_zero, Finset.sum_const_zero, add_zero] at hc
  have hd := cf3_div_sum p (x i0) (fun s'' => g s''.nd - g (x i0).nd)
  simp only [] at hd
  have h2 : ∀ (s' : Site p.c p.N) (c0 : ℝ),
      ∑ o, (cf3 p).ps s' o * (g ((cf3 p).d1 s' o).nd - c0) = g s'.nd - c0 := fun s' c0 => by
    show ∑ o, (cf3 p).ps s' o * (g s'.nd - c0) = _
    rw [← Finset.sum_mul, cf3_ps_sum, one_mul]
  have h3 : ∀ d : Site p.c p.N, g ((cf3 p).merge (x i0) d).nd - g (x i0).nd = 0 :=
    fun _ => sub_self _
  simp only [h2, h3, mul_zero, Finset.sum_const_zero, ite_self, add_zero]
  rw [hc, hd, ← Finset.sum_mul]
  have hs : 0 ≤ ∑ j, (x i0).u j * (x i0).r :=
    Finset.sum_nonneg fun j _ => mul_nonneg ((x i0).u_nonneg j) (x i0).r_nonneg
  nlinarith [mul_nonneg hs (sub_nonneg.2 (hgm (x i0).nd))]

/-! ### B3: the service ledger -/

/-- rate constant of the transitions that can change the service potential -/
def Hs (p : Par) : ℝ := p.α * p.c * p.N * (9 / 16) + p.β * p.c + (2 * p.c + 2)

theorem svc_chem (j : Fin p.c) (g : ℕ → ℝ) (ρ : ℝ) (s : Site p.c p.N) :
    ∑ k, (cf3 p).rc s k * (g (((cf3 p).tc s k).q j) * (if ((cf3 p).tc s k).R then ρ else 1)
        - g (s.q j) * (if s.R then ρ else 1))
    = ((∑ j', p.α * s.r * ((s.a j' : ℕ) : ℝ) * (1 - s.u j'))
          + ∑ j', p.α / 2 * s.r * ((s.a j' : ℕ) : ℝ))
        * (g (s.q j) - g (s.q j) * (if s.R then ρ else 1))
      + p.β * s.r * s.u j * (g (s.q j + 1) - g (s.q j) * (if s.R then ρ else 1))
      + p.β * s.r * Uf s j * (g (s.q j) - g (s.q j) * (if s.R then ρ else 1))
      + p.β * s.r * (g (s.q j) - g (s.q j) * (if s.R then ρ else 1))
      + p.β * (1 - s.r) * (g (s.q j) * ρ - g (s.q j) * (if s.R then ρ else 1)) := by
  have hc := cf3_chem_sum p s
    (fun s' => g (s'.q j) * (if s'.R then ρ else 1) - g (s.q j) * (if s.R then ρ else 1))
  simp only [Bool.false_eq_true, ite_false, ite_true, mul_one, sub_self, mul_zero,
    Finset.sum_const_zero, add_zero, zero_add] at hc
  rw [hc, ← Finset.sum_mul, ← Finset.sum_mul,
    sum_updG s.q j (fun j' => p.β * s.u j' * s.r) (fun j' => s.q j' + 1) g]
  have hU : (∑ j', if j' = j then 0 else p.β * s.u j' * s.r) = p.β * s.r * Uf s j := by
    unfold Uf
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j' _ => by split_ifs <;> ring
  rw [hU]
  ring

theorem svc_ite_le (g : ℕ → ℝ) (hg0 : ∀ n, 0 ≤ g n) (ρ : ℝ) (hρ1 : ρ ≤ 1) (n : ℕ) (b : Bool) :
    g n * (if b then ρ else 1) ≤ g n := by
  have h : (if b = true then ρ else 1) ≤ 1 := by split_ifs <;> linarith
  nlinarith [hg0 n]

theorem svc_split (j : Fin p.c) (g : ℕ → ℝ) (hg0 : ∀ n, 0 ≤ g n) (ρ : ℝ) (hρ1 : ρ ≤ 1)
    (s' : Site p.c p.N) (c0 : ℝ) :
    ∑ o, (cf3 p).ps s' o *
        (g (((cf3 p).d1 s' o).q j) * (if ((cf3 p).d1 s' o).R then ρ else 1) - c0)
      ≤ g (s'.q j) - c0 := by
  have h : ∑ o, (cf3 p).ps s' o *
        (g (((cf3 p).d1 s' o).q j) * (if ((cf3 p).d1 s' o).R then ρ else 1) - c0)
      ≤ ∑ o, (cf3 p).ps s' o * (g (s'.q j) - c0) :=
    Finset.sum_le_sum fun o _ => mul_le_mul_of_nonneg_left
      (sub_le_sub_right (svc_ite_le g hg0 ρ hρ1 (s'.q j) _) _) (cf3_ps_nonneg s' o)
  rw [← Finset.sum_mul, cf3_ps_sum, one_mul] at h
  exact h

theorem svc_div (j : Fin p.c) (g : ℕ → ℝ) (hg0 : ∀ n, 0 ≤ g n) (ρ : ℝ) (hρ1 : ρ ≤ 1)
    (s : Site p.c p.N) :
    ∑ k, (cf3 p).rd s k * ∑ o, (cf3 p).ps ((cf3 p).td s k) o *
        (g (((cf3 p).d1 ((cf3 p).td s k) o).q j)
            * (if ((cf3 p).d1 ((cf3 p).td s k) o).R then ρ else 1)
          - g (s.q j) * (if s.R then ρ else 1))
    ≤ (g (s.q j) - g (s.q j) * (if s.R then ρ else 1))
      + s.r * s.u j * (g (s.q j + 1) - g (s.q j) * (if s.R then ρ else 1))
      + s.r * Uf s j * (g (s.q j) - g (s.q j) * (if s.R then ρ else 1)) := by
  have hd := cf3_div_sum p s (fun s'' => g (s''.q j) - g (s.q j) * (if s.R then ρ else 1))
  simp only [] at hd
  refine (Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
    (svc_split j g hg0 ρ hρ1 _ _) (cf3_rd_nonneg s k)).trans (le_of_eq ?_)
  rw [hd, sum_updG s.q j (fun j' => s.u j' * s.r) (fun j' => s.q j' + 1) g]
  have hU : (∑ j', if j' = j then 0 else s.u j' * s.r) = s.r * Uf s j := by
    unfold Uf
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j' _ => by split_ifs <;> ring
  rw [hU]
  ring

theorem svc_victim (hp : p.Valid) (j : Fin p.c) (g : ℕ → ℝ) (hg0 : ∀ n, 0 ≤ g n) (ρ : ℝ)
    (hρ1 : ρ ≤ 1) (i0 : Fin p.M) (x : Fin p.M → Site p.c p.N) :
    (∑ i, if i = i0 then 0 else
        ∑ k, (cf3 p).rd (x i) k * ∑ o, (cf3 p).ps ((cf3 p).td (x i) k) o *
          ((1 / ((p.M : ℝ) - 1)) *
            (g (((cf3 p).merge (x i0) ((cf3 p).d2 ((cf3 p).td (x i) k) o)).q j)
                * (if ((cf3 p).merge (x i0) ((cf3 p).d2 ((cf3 p).td (x i) k) o)).R
                    then ρ else 1)
              - g ((x i0).q j) * (if (x i0).R then ρ else 1))))
      ≤ (1 + (p.c : ℝ)) * (g ((x i0).q j) - g ((x i0).q j) * (if (x i0).R then ρ else 1)) := by
  have hM1 := one_div_pos.mpr (cast_sub_one_pos hp.hM)
  have hD : 0 ≤ g ((x i0).q j) - g ((x i0).q j) * (if (x i0).R then ρ else 1) :=
    sub_nonneg.2 (svc_ite_le g hg0 ρ hρ1 _ _)
  refine le_of_le_of_eq (Finset.sum_le_sum (g := fun i => if i = i0 then 0 else
    (1 / ((p.M : ℝ) - 1)) * ((1 + (p.c : ℝ)) *
      (g ((x i0).q j) - g ((x i0).q j) * (if (x i0).R then ρ else 1)))) fun i _ => ?_)
    (sum_victim_const hp.hM i0 _)
  by_cases h : i = i0
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]
    have inner : ∀ k, ∑ o, (cf3 p).ps ((cf3 p).td (x i) k) o *
          ((1 / ((p.M : ℝ) - 1)) *
            (g (((cf3 p).merge (x i0) ((cf3 p).d2 ((cf3 p).td (x i) k) o)).q j)
                * (if ((cf3 p).merge (x i0) ((cf3 p).d2 ((cf3 p).td (x i) k) o)).R
                    then ρ else 1)
              - g ((x i0).q j) * (if (x i0).R then ρ else 1)))
        ≤ (1 / ((p.M : ℝ) - 1)) *
            (g ((x i0).q j) - g ((x i0).q j) * (if (x i0).R then ρ else 1)) := by
      intro k
      have h1 : ∑ o, (cf3 p).ps ((cf3 p).td (x i) k) o *
          ((1 / ((p.M : ℝ) - 1)) *
            (g (((cf3 p).merge (x i0) ((cf3 p).d2 ((cf3 p).td (x i) k) o)).q j)
                * (if ((cf3 p).merge (x i0) ((cf3 p).d2 ((cf3 p).td (x i) k) o)).R
                    then ρ else 1)
              - g ((x i0).q j) * (if (x i0).R then ρ else 1)))
          ≤ ∑ o, (cf3 p).ps ((cf3 p).td (x i) k) o * ((1 / ((p.M : ℝ) - 1)) *
            (g ((x i0).q j) - g ((x i0).q j) * (if (x i0).R then ρ else 1))) :=
        Finset.sum_le_sum fun o _ => mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (sub_le_sub_right (svc_ite_le g hg0 ρ hρ1 ((x i0).q j) _) _) hM1.le)
          (cf3_ps_nonneg _ _)
      rw [← Finset.sum_mul, cf3_ps_sum, one_mul] at h1
      exact h1
    have h2 : ∑ k, (cf3 p).rd (x i) k * ∑ o, (cf3 p).ps ((cf3 p).td (x i) k) o *
          ((1 / ((p.M : ℝ) - 1)) *
            (g (((cf3 p).merge (x i0) ((cf3 p).d2 ((cf3 p).td (x i) k) o)).q j)
                * (if ((cf3 p).merge (x i0) ((cf3 p).d2 ((cf3 p).td (x i) k) o)).R
                    then ρ else 1)
              - g ((x i0).q j) * (if (x i0).R then ρ else 1)))
        ≤ ∑ k, (cf3 p).rd (x i) k * ((1 / ((p.M : ℝ) - 1)) *
            (g ((x i0).q j) - g ((x i0).q j) * (if (x i0).R then ρ else 1))) :=
      Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (inner k) (cf3_rd_nonneg _ _)
    rw [← Finset.sum_mul] at h2
    have h3 := mul_le_mul_of_nonneg_right (cf3_rd_sum_le (x i)) (mul_nonneg hM1.le hD)
    linarith

theorem svc_S_bound (hp : p.Valid) (s : Site p.c p.N) :
    (∑ j', p.α * s.r * ((s.a j' : ℕ) : ℝ) * (1 - s.u j'))
      + ∑ j', p.α / 2 * s.r * ((s.a j' : ℕ) : ℝ) ≤ p.α * p.c * p.N * (9 / 16) := by
  rw [← Finset.sum_add_distrib]
  have key : ∀ j' : Fin p.c, p.α * s.r * ((s.a j' : ℕ) : ℝ) * (1 - s.u j')
      + p.α / 2 * s.r * ((s.a j' : ℕ) : ℝ) ≤ p.α * p.N * (9 / 16) := by
    intro j'
    have h1 := s.a_three_halves_le hp.hN j'
    have h0 := s.a_three_halves_nonneg j'
    have h2 : s.r * (((s.a j' : ℕ) : ℝ) * (3 / 2 - s.u j')) ≤ p.N * (9 / 16) := by
      nlinarith [mul_nonneg (sub_nonneg.2 s.r_le_one) h0]
    have h3 := mul_le_mul_of_nonneg_left h2 hp.hα
    linarith
  have hs := Finset.sum_le_sum fun j' (_ : j' ∈ (Finset.univ : Finset (Fin p.c))) => key j'
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  linarith

/-- B3, fuel absent at the site. -/
theorem cf3Gen_service_off (hp : p.Valid) (i0 : Fin p.M) (j : Fin p.c) (g : ℕ → ℝ)
    (hg0 : ∀ n, 0 ≤ g n) (ρ : ℝ) (hρ1 : ρ ≤ 1) (x : Fin p.M → Site p.c p.N)
    (hR : (x i0).R = false) :
    cf3Gen p (fun z => g ((z i0).q j) * (if (z i0).R then ρ else 1)) x
      ≤ -(p.β * (1 - ρ) * g ((x i0).q j)) := by
  unfold cf3Gen
  refine le_of_eq_of_le (popGen_single (cf3 p) p.M hp.hM i0
    (fun s => g (s.q j) * (if s.R then ρ else 1)) x) ?_
  refine (add_le_add (add_le_add (le_of_eq (svc_chem j g ρ (x i0)))
    (svc_div j g hg0 ρ hρ1 (x i0))) (svc_victim hp j g hg0 ρ hρ1 i0 x)).trans ?_
  have hr : (x i0).r = 0 := by simp [Site.r, hR]
  rw [hr, hR]
  simp only [Bool.false_eq_true, ite_false, mul_one]
  linarith

/-- B3, fuel present at the site. -/
theorem cf3Gen_service_on (hp : p.Valid) (i0 : Fin p.M) (j : Fin p.c) (g : ℕ → ℝ)
    (hg0 : ∀ n, 0 ≤ g n) (ρ : ℝ) (hρ1 : ρ ≤ 1) (x : Fin p.M → Site p.c p.N)
    (hR : (x i0).R = true) :
    cf3Gen p (fun z => g ((z i0).q j) * (if (z i0).R then ρ else 1)) x
      ≤ (p.β + 1) * (x i0).u j * (g ((x i0).q j + 1) - ρ * g ((x i0).q j))
        + Hs p * (1 - ρ) * g ((x i0).q j) := by
  unfold cf3Gen
  refine le_of_eq_of_le (popGen_single (cf3 p) p.M hp.hM i0
    (fun s => g (s.q j) * (if s.R then ρ else 1)) x) ?_
  refine (add_le_add (add_le_add (le_of_eq (svc_chem j g ρ (x i0)))
    (svc_div j g hg0 ρ hρ1 (x i0))) (svc_victim hp j g hg0 ρ hρ1 i0 x)).trans ?_
  have hr : (x i0).r = 1 := by simp [Site.r, hR]
  have hS := svc_S_bound hp (x i0)
  have hU0 := Uf_nonneg (x i0) j
  have hU1 := Uf_le (x i0) j
  have hD : 0 ≤ (1 - ρ) * g ((x i0).q j) := mul_nonneg (by linarith) (hg0 _)
  rw [hr] at hS
  rw [hr, hR]
  simp only [ite_true, mul_one] at hS ⊢
  have hβU := mul_le_mul_of_nonneg_left hU1 hp.hβ
  have hK : (∑ j', p.α * (((x i0).a j' : ℕ) : ℝ) * (1 - (x i0).u j'))
      + (∑ j', p.α / 2 * (((x i0).a j' : ℕ) : ℝ))
      + p.β * Uf (x i0) j + p.β + 1 + Uf (x i0) j + 1 + p.c ≤ Hs p := by
    unfold Hs
    linarith
  have hprod := mul_le_mul_of_nonneg_right hK hD
  linarith

end

end FunctionalCapacity

#print axioms FunctionalCapacity.cf3Gen_div

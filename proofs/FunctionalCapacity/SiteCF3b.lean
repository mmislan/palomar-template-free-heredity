module

public import proofs.FunctionalCapacity.SiteCF3

@[expose] public section

/-!
# CF3: the species potential (branching drift of one species)
-/

namespace FunctionalCapacity

noncomputable section
open Finset

variable {p : Par}

/-- foreign trigger load seen by species `j` -/
def Uf {c N : ℕ} (s : Site c N) (j : Fin c) : ℝ := ∑ j', if j' = j then 0 else s.u j'

/-- foreign discharge load seen by species `j` -/
def Hf (p : Par) (s : Site p.c p.N) (j : Fin p.c) : ℝ :=
  ∑ j', if j' = j then 0 else (p.β * s.u j' + p.α * ((s.a j' : ℕ) : ℝ) * (3 / 2 - s.u j'))

theorem Uf_nonneg {c N : ℕ} (s : Site c N) (j : Fin c) : 0 ≤ Uf s j :=
  Finset.sum_nonneg fun j' _ => by
    split_ifs
    · exact le_rfl
    · exact s.u_nonneg j'

theorem Uf_le {c N : ℕ} (s : Site c N) (j : Fin c) : Uf s j ≤ (c : ℝ) - 1 := by
  have h : Uf s j ≤ ∑ j' : Fin c, if j' = j then (0 : ℝ) else 1 :=
    Finset.sum_le_sum fun j' _ => by
      split_ifs
      · exact le_rfl
      · exact s.u_le_one j'
  rw [sum_ite_ne_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at h
  exact h

theorem Hf_ge (hp : p.Valid) (s : Site p.c p.N) (j : Fin p.c) : p.β * Uf s j ≤ Hf p s j := by
  unfold Uf Hf
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j' _ => ?_
  split_ifs
  · simp
  · have := mul_nonneg hp.hα (s.a_three_halves_nonneg j')
    rw [← mul_assoc] at this
    linarith

theorem Hf_le (hp : p.Valid) (s : Site p.c p.N) (j : Fin p.c) :
    Hf p s j ≤ p.β * Uf s j + p.α * p.N * (9 / 16) * ((p.c : ℝ) - 1) := by
  have h : Hf p s j ≤ ∑ j' : Fin p.c, ((if j' = j then 0 else p.β * s.u j')
      + (if j' = j then 0 else p.α * p.N * (9 / 16))) := by
    unfold Hf
    refine Finset.sum_le_sum fun j' _ => ?_
    split_ifs
    · simp
    · have := mul_le_mul_of_nonneg_left (s.a_three_halves_le hp.hN j') hp.hα
      linarith
  rw [Finset.sum_add_distrib, sum_ite_ne_zero j (fun _ => p.α * p.N * (9 / 16)), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have h2 : p.β * Uf s j = ∑ j', if j' = j then 0 else p.β * s.u j' := by
    unfold Uf
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j' _ => by split_ifs <;> simp
  rw [h2]
  linarith

/-! ### Evaluation of channel sums on a function of one species -/

theorem sum_upd {c N : ℕ} (a : Fin c → Fin (N + 1)) (j : Fin c) (cf : Fin c → ℝ)
    (v : Fin c → Fin (N + 1)) (G : ℕ → ℝ) (c0 : ℝ) :
    ∑ j', cf j' * (G ((Function.update a j' (v j') j : Fin (N + 1)) : ℕ) - c0)
      = cf j * (G (v j : ℕ) - c0)
        + (∑ j', if j' = j then 0 else cf j') * (G (a j : ℕ) - c0) := by
  rw [sum_split j (fun j' => cf j' * (G ((Function.update a j' (v j') j : Fin (N + 1)) : ℕ) - c0)),
    Function.update_self, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun j' _ => ?_
  split_ifs with h
  · simp
  · rw [Function.update_of_ne (Ne.symm h)]

theorem inc_term {c N : ℕ} (hN : 0 < N) (s : Site c N) (j : Fin c) (cc c0 : ℝ) (G : ℕ → ℝ) :
    cc * (1 - s.u j) * (G ((Site.inc (s.a j) : Fin (N + 1)) : ℕ) - c0)
      = cc * (1 - s.u j) * (G ((s.a j : ℕ) + 1) - c0) := by
  by_cases h : (s.a j : ℕ) < N
  · have e : ((Site.inc (s.a j) : Fin (N + 1)) : ℕ) = (s.a j : ℕ) + 1 := Nat.min_eq_left h
    rw [e]
  · have h2 := (s.a j).isLt
    have e : (s.a j : ℕ) = N := by omega
    have hu : s.u j = 1 := by
      unfold Site.u
      rw [e]
      exact div_self (by exact_mod_cast hN.ne')
    rw [hu]
    ring

/-- the within-site channels acting on a potential of species `j` and the fuel -/
theorem species_chem (hp : p.Valid) (j : Fin p.c) (W : ℕ → Bool → ℝ) (s : Site p.c p.N) :
    ∑ k, (cf3 p).rc s k * (W (((cf3 p).tc s k).a j) ((cf3 p).tc s k).R - W (s.a j) s.R)
    = p.ε * (1 - s.u j) * (W ((s.a j : ℕ) + 1) s.R - W (s.a j) s.R)
      + p.α * s.r * ((s.a j : ℕ) : ℝ) * (1 - s.u j) * (W ((s.a j : ℕ) + 1) false - W (s.a j) s.R)
      + p.α / 2 * s.r * ((s.a j : ℕ) : ℝ) * (W ((s.a j : ℕ) - 1) false - W (s.a j) s.R)
      + ((s.a j : ℕ) : ℝ) * (W ((s.a j : ℕ) - 1) s.R - W (s.a j) s.R)
      + (p.β * s.r * (1 + s.u j) + s.r * Hf p s j) * (W (s.a j) false - W (s.a j) s.R)
      + p.β * (1 - s.r) * (W (s.a j) true - W (s.a j) s.R) := by
  have hc := cf3_chem_sum p s (fun s' => W (s'.a j) s'.R - W (s.a j) s.R)
  simp only [] at hc
  rw [hc,
    sum_upd s.a j (fun j' => p.ε * (1 - s.u j')) (fun j' => Site.inc (s.a j'))
      (fun n => W n s.R),
    sum_upd s.a j (fun j' => p.α * s.r * ((s.a j' : ℕ) : ℝ) * (1 - s.u j'))
      (fun j' => Site.inc (s.a j')) (fun n => W n false),
    sum_upd s.a j (fun j' => p.α / 2 * s.r * ((s.a j' : ℕ) : ℝ)) (fun j' => Site.dec (s.a j'))
      (fun n => W n false),
    sum_upd s.a j (fun j' => ((s.a j' : ℕ) : ℝ)) (fun j' => Site.dec (s.a j'))
      (fun n => W n s.R),
    inc_term hp.hN s j p.ε (W (s.a j) s.R) (fun n => W n s.R),
    inc_term hp.hN s j (p.α * s.r * ((s.a j : ℕ) : ℝ)) (W (s.a j) s.R) (fun n => W n false)]
  have hdec : ((Site.dec (s.a j) : Fin (p.N + 1)) : ℕ) = (s.a j : ℕ) - 1 := rfl
  rw [hdec]
  have e5 : ∑ j', p.β * s.u j' * s.r * (W (s.a j) false - W (s.a j) s.R)
      = p.β * s.r * (s.u j + Uf s j) * (W (s.a j) false - W (s.a j) s.R) := by
    rw [show s.u j + Uf s j = ∑ j', s.u j' from (sum_split j _).symm, Finset.mul_sum,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hHf : s.r * Hf p s j
      = (∑ j', if j' = j then 0 else p.α * s.r * ((s.a j' : ℕ) : ℝ) * (1 - s.u j'))
        + (∑ j', if j' = j then 0 else p.α / 2 * s.r * ((s.a j' : ℕ) : ℝ))
        + p.β * s.r * Uf s j := by
    unfold Hf Uf
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j' _ => by split_ifs <;> ring
  rw [e5]
  linear_combination (-(W (s.a j) false - W (s.a j) s.R)) * hHf

/-- both daughters of a split, for a potential of species `j` and the fuel -/
theorem split_species (j : Fin p.c) (W : ℕ → Bool → ℝ) (s' : Site p.c p.N) (c0 V : ℝ) :
    ∑ o, (cf3 p).ps s' o *
        ((W (((cf3 p).d1 s' o).a j) ((cf3 p).d1 s' o).R - c0)
          + (W (((cf3 p).d2 s' o).a j) ((cf3 p).d2 s' o).R - V))
      = binE (fun k => W k s'.R) (s'.a j) + binE (fun k => W k false) (s'.a j) - c0 - V := by
  have hm := cf3_ps_marg s' j
    (fun k b => W k (s'.R && b) + W ((s'.a j : ℕ) - k) (s'.R && !b))
  simp only [Bool.and_true, Bool.and_false, Bool.not_true, Bool.not_false] at hm
  rw [binE_add, binE_add, binE_reflect (fun k => W k false),
    binE_reflect (fun k => W k s'.R)] at hm
  have h1 : ∀ o : Split p.c p.N, (cf3 p).ps s' o *
        ((W (((cf3 p).d1 s' o).a j) ((cf3 p).d1 s' o).R - c0)
          + (W (((cf3 p).d2 s' o).a j) ((cf3 p).d2 s' o).R - V))
      = (cf3 p).ps s' o * (W (o.1 j) (s'.R && o.2)
          + W ((s'.a j : ℕ) - (o.1 j : ℕ)) (s'.R && !o.2)) - (cf3 p).ps s' o * (c0 + V) := by
    intro o
    show (cf3 p).ps s' o * ((W (o.1 j) (s'.R && o.2) - c0)
      + (W ((s'.a j : ℕ) - (o.1 j : ℕ)) (s'.R && !o.2) - V)) = _
    ring
  rw [Finset.sum_congr rfl fun o _ => h1 o, Finset.sum_sub_distrib, hm, ← Finset.sum_mul,
    cf3_ps_sum]
  ring

/-- site-level form of the species drift: all events initiated at one site, with the victim
average `V` of the potential -/
theorem species_site (hp : p.Valid) (j : Fin p.c) (W : ℕ → Bool → ℝ) (s : Site p.c p.N) (V : ℝ)
    (hV : 0 ≤ V) :
    (∑ k, (cf3 p).rc s k * (W (((cf3 p).tc s k).a j) ((cf3 p).tc s k).R - W (s.a j) s.R))
    + ∑ k, (cf3 p).rd s k * ∑ o, (cf3 p).ps ((cf3 p).td s k) o *
        ((W (((cf3 p).d1 ((cf3 p).td s k) o).a j) ((cf3 p).d1 ((cf3 p).td s k) o).R
            - W (s.a j) s.R)
          + (W (((cf3 p).d2 ((cf3 p).td s k) o).a j) ((cf3 p).d2 ((cf3 p).td s k) o).R - V))
    ≤ siteOp p W (s.a j) s.R (Hf p s j) (Uf s j) + W (s.a j) s.R - V := by
  have hd := cf3_div_sum p s (fun s'' => binE (fun k => W k s''.R) (s''.a j)
    + binE (fun k => W k false) (s''.a j) - W (s.a j) s.R - V)
  simp only [] at hd
  simp only [split_species]
  rw [species_chem hp j W s, hd]
  have e6 : ∑ j', s.u j' * s.r * (binE (fun k => W k false) (s.a j)
        + binE (fun k => W k false) (s.a j) - W (s.a j) s.R - V)
      = (s.u j + Uf s j) * s.r * (binE (fun k => W k false) (s.a j)
        + binE (fun k => W k false) (s.a j) - W (s.a j) s.R - V) := by
    rw [← Finset.sum_mul, ← Finset.sum_mul, sum_split j (fun j' => s.u j')]
    rfl
  rw [e6]
  have hu : s.u j = ((s.a j : ℕ) : ℝ) / (p.N : ℝ) := rfl
  have hu0 : 0 ≤ ((s.a j : ℕ) : ℝ) / (p.N : ℝ) := s.u_nonneg j
  have hprod := mul_nonneg (add_nonneg hu0 (Uf_nonneg s j)) hV
  cases hR : s.R
  · have hr : s.r = 0 := by simp [Site.r, hR]
    rw [hr]
    simp only [siteOp, hu, Bool.false_eq_true, ite_false]
    nlinarith [hprod]
  · have hr : s.r = 1 := by simp [Site.r, hR]
    rw [hr]
    simp only [siteOp, hu, ite_true]
    nlinarith [hprod]

/-- B2: the species potential. -/
theorem cf3Gen_species_le (hp : p.Valid) (j : Fin p.c) (W : ℕ → Bool → ℝ)
    (hW : ∀ a R, 0 ≤ W a R) (x : Fin p.M → Site p.c p.N) :
    cf3Gen p (fun z => ∑ i, W ((z i).a j) (z i).R) x
      ≤ ∑ i, siteOp p W ((x i).a j) (x i).R (Hf p (x i) j) (Uf (x i) j) := by
  unfold cf3Gen
  refine le_of_eq_of_le (popGen_additive (cf3 p) p.M hp.hM (fun s => W (s.a j) s.R) x) ?_
  have hV : ∀ i : Fin p.M, 0 ≤ (1 / ((p.M : ℝ) - 1)) *
      ∑ v, if v = i then 0 else W ((x v).a j) (x v).R := fun i =>
    mul_nonneg (one_div_pos.mpr (cast_sub_one_pos hp.hM)).le
      (Finset.sum_nonneg fun v _ => by
        split_ifs
        · exact le_rfl
        · exact hW _ _)
  refine (Finset.sum_le_sum (g := fun i =>
    siteOp p W ((x i).a j) (x i).R (Hf p (x i) j) (Uf (x i) j) + W ((x i).a j) (x i).R
      - (1 / ((p.M : ℝ) - 1)) * ∑ v, if v = i then 0 else W ((x v).a j) (x v).R)
    fun i _ => ?_).trans (le_of_eq ?_)
  · refine le_of_eq_of_le ?_ (species_site hp j W (x i) _ (hV i))
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun o _ => ?_
    congr 1
    congr 1
    exact victim_avg hp.hM i
      (W (((cf3 p).d2 ((cf3 p).td (x i) k) o).a j) ((cf3 p).d2 ((cf3 p).td (x i) k) o).R)
      (fun v => W ((x v).a j) (x v).R)
  · rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      sum_victim_avg hp.hM (fun v => W ((x v).a j) (x v).R)]
    ring

end

end FunctionalCapacity

#print axioms FunctionalCapacity.cf3Gen_species_le

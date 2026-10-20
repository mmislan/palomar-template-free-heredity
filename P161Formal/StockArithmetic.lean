module

public import P161Formal.Quantitative

/-! Exact occupation-sensitive feed tilt and global seed/division exponents.
These analytic comparisons do not assert moment bounds on a process.
The accepted-feed calculation uses the fuel occupation weight, not a
Poisson bound at the maximal recharge intensity. -/

@[expose] public section
namespace P161Formal
noncomputable section

def stockEta : ℝ := 1/10000
def stockS : ℝ := 400/22457607
def stockFeedK1 : ℝ := 73830428000000/224557612393
def stockFeedK2 : ℝ :=
  (18457604 + 3/(1-stockS)) * stockS/(1-stockS)

theorem stock_tilt_parameters :
    0 < stockS ∧ stockS < stockEta ∧ stockEta < 1 := by
  norm_num [stockS,stockEta]

theorem stock_feed_rational_comparisons :
    4000000*(stockEta-stockS)/(1-stockEta+stockS) = stockFeedK1 ∧
    stockFeedK2 ≤ stockFeedK1 ∧
    4*stockS+240*stockFeedK1-stockEta*800000000 < -1092 := by
  norm_num [stockS,stockEta,stockFeedK1,stockFeedK2]

theorem stock_feed_tilt_entries :
    4000000*(Real.exp (stockEta-stockS)-1) ≤ stockFeedK1 ∧
    (18457604+3*Real.exp stockS)*(Real.exp stockS-1) ≤ stockFeedK1 := by
  obtain ⟨hs0,hsE,hE1⟩ := stock_tilt_parameters
  have hE0 : 0 < stockEta := lt_trans hs0 hsE
  have hs1 : stockS < 1 := lt_trans hsE hE1
  have he := Real.exp_bound_div_one_sub_of_interval
    (show 0 ≤ stockEta-stockS by linarith) (show stockEta-stockS < 1 by linarith)
  have hs := Real.exp_bound_div_one_sub_of_interval (le_of_lt hs0) hs1
  have hnon : 0 ≤ Real.exp stockS - 1 := by
    have h := Real.add_one_le_exp stockS
    linarith
  obtain ⟨hid,hk,hfinal⟩ := stock_feed_rational_comparisons
  constructor
  · have hrat : 4000000*(1/(1-(stockEta-stockS))-1) = stockFeedK1 := by
      norm_num [stockS,stockEta,stockFeedK1]
    nlinarith
  · have hmul := mul_le_mul
      (show 18457604+3*Real.exp stockS ≤ 18457604+3/(1-stockS) by
        have h3 : 3*Real.exp stockS ≤ 3/(1-stockS) := by
          simpa only [div_eq_mul_inv,one_mul] using
            mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ 3 by norm_num)
        linarith)
      (show Real.exp stockS-1 ≤ stockS/(1-stockS) by
        have hh : 1/(1-stockS)-1 = stockS/(1-stockS) := by norm_num [stockS]
        linarith)
      hnon (show 0 ≤ 18457604+3/(1-stockS) by norm_num [stockS])
    exact le_trans (by simpa only [stockFeedK2,div_eq_mul_inv,mul_assoc] using hmul) hk

theorem stock_feed_exponent :
    4*stockS + 240 * max (4000000*(Real.exp (stockEta-stockS)-1))
      ((18457604+3*Real.exp stockS)*(Real.exp stockS-1)) - stockEta*800000000 ≤ -20 := by
  obtain ⟨h1,h2⟩ := stock_feed_tilt_entries
  have hm := max_le h1 h2
  have hf := stock_feed_rational_comparisons.2.2
  linarith

theorem stock_seed_exponent :
    4320*(Real.exp (1/10)-1) - (1/10 : ℝ)*5000 ≤ -20 := by
  have h := Real.exp_bound_div_one_sub_of_interval (x := (1/10 : ℝ))
    (by norm_num) (by norm_num)
  norm_num at h
  linarith

theorem stock_division_exp_bound : Real.exp (1/5) - 1 ≤ (31/140 : ℝ) := by
  have h := Real.exp_bound' (x := (1/5 : ℝ)) (by norm_num) (by norm_num) (n := 4) (by decide)
  norm_num [Finset.sum_range_succ, Nat.factorial_succ] at h
  linarith

theorem stock_division_exponent :
    960*(Real.exp (1/5)-1) - (1/5 : ℝ)*1200 ≤ -(192/7 : ℝ) ∧
    -(192/7 : ℝ) < -20 := by
  have h := stock_division_exp_bound
  constructor <;> linarith

end
end P161Formal

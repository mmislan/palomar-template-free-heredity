module

public import P161Formal.CountedWords
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Tactic.FieldSimp

/-! Exact Poisson mixture of the counted-word majorant. This series identity
does not identify a source path event or assume a recovery probability law. -/

@[expose] public section
namespace P161Formal
open scoped BigOperators
noncomputable section

def poissonWordTerm (mu a b : ℝ) (j n : ℕ) : ℝ :=
  (Real.exp (-mu)*mu^n/n.factorial)*binomialWordCoefficient n j a b

theorem poisson_word_shift (mu a b : ℝ) (j m : ℕ) :
    poissonWordTerm mu a b j (m+j) =
      (Real.exp (-mu)*(mu*b)^j/j.factorial)*((mu*a)^m/m.factorial) := by
  have hm : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hj : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hsum : ((m+j).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (m+j)
  simp only [poissonWordTerm,binomialWordCoefficient,Nat.cast_choose ℝ (show j ≤ m+j by omega),
    Nat.add_sub_cancel,pow_add,mul_pow]
  field_simp [hm,hj,hsum]

theorem poisson_word_hasSum (mu a b : ℝ) (j : ℕ) :
    HasSum (poissonWordTerm mu a b j)
      (Real.exp (mu*(a-1))*(mu*b)^j/j.factorial) := by
  let C : ℝ := Real.exp (-mu)*(mu*b)^j/j.factorial
  have he : HasSum (fun m : ℕ => (mu*a)^m/m.factorial) (Real.exp (mu*a)) := by
    simpa only [←Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (mu*a)
  have hshift : HasSum (fun m => poissonWordTerm mu a b j (m+j)) (C*Real.exp (mu*a)) := by
    exact (he.mul_left C).congr_fun (fun m => poisson_word_shift mu a b j m)
  have hzero : ∑ n ∈ Finset.range j, poissonWordTerm mu a b j n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hnj := Finset.mem_range.mp hn
    simp only [poissonWordTerm,binomialWordCoefficient,Nat.choose_eq_zero_of_lt hnj,
      Nat.cast_zero,zero_mul,mul_zero]
  have hfull := (hasSum_nat_add_iff j).mp hshift
  rw [hzero,add_zero] at hfull
  have hexp : Real.exp (-mu)*Real.exp (mu*a) = Real.exp (mu*(a-1)) := by
    rw [←Real.exp_add]
    congr 1
    ring
  have hvalue : C*Real.exp (mu*a) = Real.exp (mu*(a-1))*(mu*b)^j/j.factorial := by
    calc
      C*Real.exp (mu*a) = (Real.exp (-mu)*Real.exp (mu*a))*(mu*b)^j/j.factorial := by
        dsimp [C]
        ring
      _ = _ := by rw [hexp]
  simpa only [hvalue] using hfull

theorem poisson_word_tsum (mu a b : ℝ) (j : ℕ) :
    (∑' n, poissonWordTerm mu a b j n) =
      Real.exp (mu*(a-1))*(mu*b)^j/j.factorial :=
  (poisson_word_hasSum mu a b j).tsum_eq

end
end P161Formal

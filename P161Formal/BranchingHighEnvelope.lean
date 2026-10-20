module

public import P161Formal.BranchingBernstein
public import Mathlib.Tactic.FieldSimp

/-! Connect the degree-six positivity certificate to the beta4m high-count
scalar envelope. The actual binomial/source comparisons remain separate.
Pending strict verification; no stochastic success law is a premise. -/

@[expose] public section
namespace P161Formal

def branchingHighUnfueledEnvelope (x : ℚ) : ℚ :=
  (1860480 / ((x+1)*(x+2)*(x+3)*(x+4)*(x+5))) *
    ((1+70/4000000)*(135/2)-70)

def branchingHighFueledEnvelope (x : ℚ) : ℚ :=
  let c : ℚ := 1 + 70/4000000
  let u := x/2048
  let A := 1860480 / ((x+1)*(x+2)*(x+3)*(x+4)*(x+5))
  A * (5 + 800*x*(1-u)*(c*(x+1)/(x+6)-1) +
    400*x*(c-1)+2000*c + 70*(3+u)+70*1843200/4000000 +
    32*c+30 + (u+2)*(64*c-1) + 1/2)

theorem branching_fueled_envelope_identity (x : ℚ) (hx : 13 ≤ x) :
    branchingHighFueledEnvelope x =
      1860480 * branchingFueledNumerator x / branchingDenominatorSix x := by
  have h1 : x+1 ≠ 0 := by linarith
  have h2 : x+2 ≠ 0 := by linarith
  have h3 : x+3 ≠ 0 := by linarith
  have h4 : x+4 ≠ 0 := by linarith
  have h5 : x+5 ≠ 0 := by linarith
  have h6 : x+6 ≠ 0 := by linarith
  unfold branchingHighFueledEnvelope branchingFueledNumerator branchingDenominatorSix
  field_simp
  ring

theorem branching_high_envelopes (x : ℚ) (hx0 : 13 ≤ x) (hx1 : x ≤ 2048) :
    branchingHighUnfueledEnvelope x ≤ 0 ∧
    branchingHighFueledEnvelope x ≤ 13/10000000 := by
  constructor
  · have hx : 0 < x := by linarith
    have hA : 0 ≤ 1860480 / ((x+1)*(x+2)*(x+3)*(x+4)*(x+5)) := by positivity
    have hc : (1+(70:ℚ)/4000000)*(135/2)-70 ≤ 0 := by norm_num
    exact mul_nonpos_of_nonneg_of_nonpos hA hc
  · rw [branching_fueled_envelope_identity x hx0]
    exact branching_high_rational_bound x hx0 hx1

end P161Formal

module

public import P161Formal.SourceContractBridge

/-! Positive stopped proposal suboperators on an arbitrary raw state type.
Only the physical mark set is finite. Natural service/division counters need
not be finite, and no stopped success probability is an input. -/

@[expose] public section
namespace P161Formal
open scoped BigOperators
noncomputable section

def restrictedProposalApply {S R : Type} [Fintype R]
    (C : HybridCTMC.Channels S R) (Lam : ℝ)
    (live : S → Prop) [DecidablePred live]
    (keep : Option R → Prop) [DecidablePred keep] (f : S → ℝ) (x : S) : ℝ :=
  if live x then ∑ m : Option R,
    CTMCHeredity20261019.MarkedUniformization.weight C Lam x m*
      (if keep m then
        if live (CTMCHeredity20261019.MarkedUniformization.next C x m) then
          f (CTMCHeredity20261019.MarkedUniformization.next C x m) else 0
        else 0)
    else 0

def markedSuboperator {S R : Type} [Fintype R]
    (C : HybridCTMC.Channels S R) {Lam : ℝ} (hLam : 0 < Lam)
    (bound : ∀ x, ∑ r, C.propensity x r ≤ Lam)
    (live : S → Prop) [DecidablePred live]
    (keep : Option R → Prop) [DecidablePred keep] : FunctionalCapacity.SubMarkov S where
  P := restrictedProposalApply C Lam live keep
  mono f g hfg x := by
    by_cases hx : live x
    · simp only [restrictedProposalApply,ite_eq_left hx]
      apply Finset.sum_le_sum
      intro m _
      apply mul_le_mul_of_nonneg_left _
        (CTMCHeredity20261019.MarkedUniformization.weight_nonneg C hLam bound x m)
      split_ifs <;> first | exact hfg _ | exact le_rfl
    · simp only [restrictedProposalApply,ite_eq_right hx]
      exact le_rfl
  add f g x := by
    by_cases hx : live x
    · simp only [restrictedProposalApply,ite_eq_left hx]
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m _
      split_ifs <;> ring
    · simp [restrictedProposalApply,hx]
  smul c f x := by
    by_cases hx : live x
    · simp only [restrictedProposalApply,ite_eq_left hx]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      split_ifs <;> ring
    · simp [restrictedProposalApply,hx]
  le_one x := by
    by_cases hx : live x
    · simp only [restrictedProposalApply,ite_eq_left hx]
      calc
        _ ≤ ∑ m : Option R, CTMCHeredity20261019.MarkedUniformization.weight C Lam x m := by
          apply Finset.sum_le_sum
          intro m _
          have hw := CTMCHeredity20261019.MarkedUniformization.weight_nonneg C hLam bound x m
          split_ifs <;> nlinarith
        _ = 1 := CTMCHeredity20261019.MarkedUniformization.weight_sum C Lam x
    · simp [restrictedProposalApply,hx]

theorem restricted_proposal_partition {S R : Type} [Fintype R]
    (C : HybridCTMC.Channels S R) (Lam : ℝ)
    (live : S → Prop) [DecidablePred live]
    (keep : Option R → Prop) [DecidablePred keep] (f : S → ℝ) (x : S) :
    restrictedProposalApply C Lam live keep f x +
      restrictedProposalApply C Lam live (fun m => ¬keep m) f x =
        restrictedProposalApply C Lam live (fun _ => True) f x := by
  by_cases hx : live x
  · simp only [restrictedProposalApply,ite_eq_left hx,ite_true]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    split_ifs <;> ring
  · simp [restrictedProposalApply,hx]

end
end P161Formal

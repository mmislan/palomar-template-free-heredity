module

public import P161Formal.BranchingProfile

/-! Cheapest representative low-count beta4m pilot: four fueled vertices at
the zero-count boundary, where the fuel correction is negative. The complete
104-vertex low-count certificate is a separate bounded check. -/

@[expose] public section
namespace P161Formal

theorem branching_low_zero_pilot :
    ([(0 : ℚ),2]).all (fun U => ([0,1843200] : List ℚ).all (fun v => decide
      (branchingSiteOperatorQ 0 true U v 6 + branchingWitnessQ 0 true/2 ≤
        (13/10000000 : ℚ)))) = true := by
  decide +kernel

end P161Formal

module

public import P161Formal.ResetCertificateInterface
public import P161Formal.ResetPilots
public import P161Formal.ResetSeparatePilot

/-! Exact literal residuals for this finite block. Each new parent is checked
by the ordinary kernel decision procedure. No native evaluator is used. -/

@[expose] public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem reset_cert_a_2048 : resetParentTest 2048 = true := by
  obtain ⟨g0, g1⟩ := separate_reset_2048
  simp [resetParentTest, g0, g1]

def resetParents2048To2048 : List ℕ := [2048]

theorem reset_block_2048_to_2048 : resetParents2048To2048.all resetParentTest = true := by
  simp only [resetParents2048To2048, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact reset_cert_a_2048

end P161Formal

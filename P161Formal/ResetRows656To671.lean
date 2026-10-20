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

theorem reset_cert_a_656 : resetParentTest 656 = true := by
  decide

theorem reset_cert_a_657 : resetParentTest 657 = true := by
  decide

theorem reset_cert_a_658 : resetParentTest 658 = true := by
  decide

theorem reset_cert_a_659 : resetParentTest 659 = true := by
  decide

theorem reset_cert_a_660 : resetParentTest 660 = true := by
  decide

theorem reset_cert_a_661 : resetParentTest 661 = true := by
  decide

theorem reset_cert_a_662 : resetParentTest 662 = true := by
  decide

theorem reset_cert_a_663 : resetParentTest 663 = true := by
  decide

theorem reset_cert_a_664 : resetParentTest 664 = true := by
  decide

theorem reset_cert_a_665 : resetParentTest 665 = true := by
  decide

theorem reset_cert_a_666 : resetParentTest 666 = true := by
  decide

theorem reset_cert_a_667 : resetParentTest 667 = true := by
  decide

theorem reset_cert_a_668 : resetParentTest 668 = true := by
  decide

theorem reset_cert_a_669 : resetParentTest 669 = true := by
  decide

theorem reset_cert_a_670 : resetParentTest 670 = true := by
  decide

theorem reset_cert_a_671 : resetParentTest 671 = true := by
  decide

def resetParents656To671 : List ℕ := [656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671]

theorem reset_block_656_to_671 : resetParents656To671.all resetParentTest = true := by
  simp only [resetParents656To671, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_656, ⟨reset_cert_a_657, ⟨reset_cert_a_658, ⟨reset_cert_a_659, ⟨reset_cert_a_660, ⟨reset_cert_a_661, ⟨reset_cert_a_662, ⟨reset_cert_a_663, ⟨reset_cert_a_664, ⟨reset_cert_a_665, ⟨reset_cert_a_666, ⟨reset_cert_a_667, ⟨reset_cert_a_668, ⟨reset_cert_a_669, ⟨reset_cert_a_670, reset_cert_a_671⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal

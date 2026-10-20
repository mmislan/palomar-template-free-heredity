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

theorem reset_cert_a_736 : resetParentTest 736 = true := by
  decide

theorem reset_cert_a_737 : resetParentTest 737 = true := by
  decide

theorem reset_cert_a_738 : resetParentTest 738 = true := by
  decide

theorem reset_cert_a_739 : resetParentTest 739 = true := by
  decide

theorem reset_cert_a_740 : resetParentTest 740 = true := by
  decide

theorem reset_cert_a_741 : resetParentTest 741 = true := by
  decide

theorem reset_cert_a_742 : resetParentTest 742 = true := by
  decide

theorem reset_cert_a_743 : resetParentTest 743 = true := by
  decide

theorem reset_cert_a_744 : resetParentTest 744 = true := by
  decide

theorem reset_cert_a_745 : resetParentTest 745 = true := by
  decide

theorem reset_cert_a_746 : resetParentTest 746 = true := by
  decide

theorem reset_cert_a_747 : resetParentTest 747 = true := by
  decide

theorem reset_cert_a_748 : resetParentTest 748 = true := by
  decide

theorem reset_cert_a_749 : resetParentTest 749 = true := by
  decide

theorem reset_cert_a_750 : resetParentTest 750 = true := by
  decide

theorem reset_cert_a_751 : resetParentTest 751 = true := by
  decide

def resetParents736To751 : List ℕ := [736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751]

theorem reset_block_736_to_751 : resetParents736To751.all resetParentTest = true := by
  simp only [resetParents736To751, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_736, ⟨reset_cert_a_737, ⟨reset_cert_a_738, ⟨reset_cert_a_739, ⟨reset_cert_a_740, ⟨reset_cert_a_741, ⟨reset_cert_a_742, ⟨reset_cert_a_743, ⟨reset_cert_a_744, ⟨reset_cert_a_745, ⟨reset_cert_a_746, ⟨reset_cert_a_747, ⟨reset_cert_a_748, ⟨reset_cert_a_749, ⟨reset_cert_a_750, reset_cert_a_751⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal

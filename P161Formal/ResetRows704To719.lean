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

theorem reset_cert_a_704 : resetParentTest 704 = true := by
  decide

theorem reset_cert_a_705 : resetParentTest 705 = true := by
  decide

theorem reset_cert_a_706 : resetParentTest 706 = true := by
  decide

theorem reset_cert_a_707 : resetParentTest 707 = true := by
  decide

theorem reset_cert_a_708 : resetParentTest 708 = true := by
  decide

theorem reset_cert_a_709 : resetParentTest 709 = true := by
  decide

theorem reset_cert_a_710 : resetParentTest 710 = true := by
  decide

theorem reset_cert_a_711 : resetParentTest 711 = true := by
  decide

theorem reset_cert_a_712 : resetParentTest 712 = true := by
  decide

theorem reset_cert_a_713 : resetParentTest 713 = true := by
  decide

theorem reset_cert_a_714 : resetParentTest 714 = true := by
  decide

theorem reset_cert_a_715 : resetParentTest 715 = true := by
  decide

theorem reset_cert_a_716 : resetParentTest 716 = true := by
  decide

theorem reset_cert_a_717 : resetParentTest 717 = true := by
  decide

theorem reset_cert_a_718 : resetParentTest 718 = true := by
  decide

theorem reset_cert_a_719 : resetParentTest 719 = true := by
  decide

def resetParents704To719 : List ℕ := [704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719]

theorem reset_block_704_to_719 : resetParents704To719.all resetParentTest = true := by
  simp only [resetParents704To719, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_704, ⟨reset_cert_a_705, ⟨reset_cert_a_706, ⟨reset_cert_a_707, ⟨reset_cert_a_708, ⟨reset_cert_a_709, ⟨reset_cert_a_710, ⟨reset_cert_a_711, ⟨reset_cert_a_712, ⟨reset_cert_a_713, ⟨reset_cert_a_714, ⟨reset_cert_a_715, ⟨reset_cert_a_716, ⟨reset_cert_a_717, ⟨reset_cert_a_718, reset_cert_a_719⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal

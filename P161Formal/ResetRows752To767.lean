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

theorem reset_cert_a_752 : resetParentTest 752 = true := by
  decide

theorem reset_cert_a_753 : resetParentTest 753 = true := by
  decide

theorem reset_cert_a_754 : resetParentTest 754 = true := by
  decide

theorem reset_cert_a_755 : resetParentTest 755 = true := by
  decide

theorem reset_cert_a_756 : resetParentTest 756 = true := by
  decide

theorem reset_cert_a_757 : resetParentTest 757 = true := by
  decide

theorem reset_cert_a_758 : resetParentTest 758 = true := by
  decide

theorem reset_cert_a_759 : resetParentTest 759 = true := by
  decide

theorem reset_cert_a_760 : resetParentTest 760 = true := by
  decide

theorem reset_cert_a_761 : resetParentTest 761 = true := by
  decide

theorem reset_cert_a_762 : resetParentTest 762 = true := by
  decide

theorem reset_cert_a_763 : resetParentTest 763 = true := by
  decide

theorem reset_cert_a_764 : resetParentTest 764 = true := by
  decide

theorem reset_cert_a_765 : resetParentTest 765 = true := by
  decide

theorem reset_cert_a_766 : resetParentTest 766 = true := by
  decide

theorem reset_cert_a_767 : resetParentTest 767 = true := by
  decide

def resetParents752To767 : List ℕ := [752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 763, 764, 765, 766, 767]

theorem reset_block_752_to_767 : resetParents752To767.all resetParentTest = true := by
  simp only [resetParents752To767, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_752, ⟨reset_cert_a_753, ⟨reset_cert_a_754, ⟨reset_cert_a_755, ⟨reset_cert_a_756, ⟨reset_cert_a_757, ⟨reset_cert_a_758, ⟨reset_cert_a_759, ⟨reset_cert_a_760, ⟨reset_cert_a_761, ⟨reset_cert_a_762, ⟨reset_cert_a_763, ⟨reset_cert_a_764, ⟨reset_cert_a_765, ⟨reset_cert_a_766, reset_cert_a_767⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal

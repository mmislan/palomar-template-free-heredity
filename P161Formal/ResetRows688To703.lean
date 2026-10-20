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

theorem reset_cert_a_688 : resetParentTest 688 = true := by
  decide

theorem reset_cert_a_689 : resetParentTest 689 = true := by
  decide

theorem reset_cert_a_690 : resetParentTest 690 = true := by
  decide

theorem reset_cert_a_691 : resetParentTest 691 = true := by
  decide

theorem reset_cert_a_692 : resetParentTest 692 = true := by
  decide

theorem reset_cert_a_693 : resetParentTest 693 = true := by
  decide

theorem reset_cert_a_694 : resetParentTest 694 = true := by
  decide

theorem reset_cert_a_695 : resetParentTest 695 = true := by
  decide

theorem reset_cert_a_696 : resetParentTest 696 = true := by
  decide

theorem reset_cert_a_697 : resetParentTest 697 = true := by
  decide

theorem reset_cert_a_698 : resetParentTest 698 = true := by
  decide

theorem reset_cert_a_699 : resetParentTest 699 = true := by
  decide

theorem reset_cert_a_700 : resetParentTest 700 = true := by
  decide

theorem reset_cert_a_701 : resetParentTest 701 = true := by
  decide

theorem reset_cert_a_702 : resetParentTest 702 = true := by
  decide

theorem reset_cert_a_703 : resetParentTest 703 = true := by
  decide

def resetParents688To703 : List ℕ := [688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703]

theorem reset_block_688_to_703 : resetParents688To703.all resetParentTest = true := by
  simp only [resetParents688To703, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_688, ⟨reset_cert_a_689, ⟨reset_cert_a_690, ⟨reset_cert_a_691, ⟨reset_cert_a_692, ⟨reset_cert_a_693, ⟨reset_cert_a_694, ⟨reset_cert_a_695, ⟨reset_cert_a_696, ⟨reset_cert_a_697, ⟨reset_cert_a_698, ⟨reset_cert_a_699, ⟨reset_cert_a_700, ⟨reset_cert_a_701, ⟨reset_cert_a_702, reset_cert_a_703⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal

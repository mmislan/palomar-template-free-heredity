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

theorem reset_cert_a_768 : resetParentTest 768 = true := by
  decide

theorem reset_cert_a_769 : resetParentTest 769 = true := by
  decide

theorem reset_cert_a_770 : resetParentTest 770 = true := by
  decide

theorem reset_cert_a_771 : resetParentTest 771 = true := by
  decide

theorem reset_cert_a_772 : resetParentTest 772 = true := by
  decide

theorem reset_cert_a_773 : resetParentTest 773 = true := by
  decide

theorem reset_cert_a_774 : resetParentTest 774 = true := by
  decide

theorem reset_cert_a_775 : resetParentTest 775 = true := by
  decide

theorem reset_cert_a_776 : resetParentTest 776 = true := by
  decide

theorem reset_cert_a_777 : resetParentTest 777 = true := by
  decide

theorem reset_cert_a_778 : resetParentTest 778 = true := by
  decide

theorem reset_cert_a_779 : resetParentTest 779 = true := by
  decide

theorem reset_cert_a_780 : resetParentTest 780 = true := by
  decide

theorem reset_cert_a_781 : resetParentTest 781 = true := by
  decide

theorem reset_cert_a_782 : resetParentTest 782 = true := by
  decide

theorem reset_cert_a_783 : resetParentTest 783 = true := by
  decide

def resetParents768To783 : List ℕ := [768, 769, 770, 771, 772, 773, 774, 775, 776, 777, 778, 779, 780, 781, 782, 783]

theorem reset_block_768_to_783 : resetParents768To783.all resetParentTest = true := by
  simp only [resetParents768To783, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_768, ⟨reset_cert_a_769, ⟨reset_cert_a_770, ⟨reset_cert_a_771, ⟨reset_cert_a_772, ⟨reset_cert_a_773, ⟨reset_cert_a_774, ⟨reset_cert_a_775, ⟨reset_cert_a_776, ⟨reset_cert_a_777, ⟨reset_cert_a_778, ⟨reset_cert_a_779, ⟨reset_cert_a_780, ⟨reset_cert_a_781, ⟨reset_cert_a_782, reset_cert_a_783⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal

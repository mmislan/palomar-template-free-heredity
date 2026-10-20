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

theorem reset_cert_a_992 : resetParentTest 992 = true := by
  decide

theorem reset_cert_a_993 : resetParentTest 993 = true := by
  decide

theorem reset_cert_a_994 : resetParentTest 994 = true := by
  decide

theorem reset_cert_a_995 : resetParentTest 995 = true := by
  decide

theorem reset_cert_a_996 : resetParentTest 996 = true := by
  decide

theorem reset_cert_a_997 : resetParentTest 997 = true := by
  decide

theorem reset_cert_a_998 : resetParentTest 998 = true := by
  decide

theorem reset_cert_a_999 : resetParentTest 999 = true := by
  decide

theorem reset_cert_a_1000 : resetParentTest 1000 = true := by
  decide

theorem reset_cert_a_1001 : resetParentTest 1001 = true := by
  decide

theorem reset_cert_a_1002 : resetParentTest 1002 = true := by
  decide

theorem reset_cert_a_1003 : resetParentTest 1003 = true := by
  decide

theorem reset_cert_a_1004 : resetParentTest 1004 = true := by
  decide

theorem reset_cert_a_1005 : resetParentTest 1005 = true := by
  decide

theorem reset_cert_a_1006 : resetParentTest 1006 = true := by
  decide

theorem reset_cert_a_1007 : resetParentTest 1007 = true := by
  decide

def resetParents992To1007 : List ℕ := [992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007]

theorem reset_block_992_to_1007 : resetParents992To1007.all resetParentTest = true := by
  simp only [resetParents992To1007, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_992, ⟨reset_cert_a_993, ⟨reset_cert_a_994, ⟨reset_cert_a_995, ⟨reset_cert_a_996, ⟨reset_cert_a_997, ⟨reset_cert_a_998, ⟨reset_cert_a_999, ⟨reset_cert_a_1000, ⟨reset_cert_a_1001, ⟨reset_cert_a_1002, ⟨reset_cert_a_1003, ⟨reset_cert_a_1004, ⟨reset_cert_a_1005, ⟨reset_cert_a_1006, reset_cert_a_1007⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal

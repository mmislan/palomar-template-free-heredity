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

theorem reset_cert_a_1024 : resetParentTest 1024 = true := by
  decide

theorem reset_cert_a_1025 : resetParentTest 1025 = true := by
  decide

theorem reset_cert_a_1026 : resetParentTest 1026 = true := by
  decide

theorem reset_cert_a_1027 : resetParentTest 1027 = true := by
  decide

theorem reset_cert_a_1028 : resetParentTest 1028 = true := by
  decide

theorem reset_cert_a_1029 : resetParentTest 1029 = true := by
  decide

theorem reset_cert_a_1030 : resetParentTest 1030 = true := by
  decide

theorem reset_cert_a_1031 : resetParentTest 1031 = true := by
  decide

theorem reset_cert_a_1032 : resetParentTest 1032 = true := by
  decide

theorem reset_cert_a_1033 : resetParentTest 1033 = true := by
  decide

theorem reset_cert_a_1034 : resetParentTest 1034 = true := by
  decide

theorem reset_cert_a_1035 : resetParentTest 1035 = true := by
  decide

theorem reset_cert_a_1036 : resetParentTest 1036 = true := by
  decide

theorem reset_cert_a_1037 : resetParentTest 1037 = true := by
  decide

theorem reset_cert_a_1038 : resetParentTest 1038 = true := by
  decide

theorem reset_cert_a_1039 : resetParentTest 1039 = true := by
  decide

def resetParents1024To1039 : List ℕ := [1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039]

theorem reset_block_1024_to_1039 : resetParents1024To1039.all resetParentTest = true := by
  simp only [resetParents1024To1039, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1024, ⟨reset_cert_a_1025, ⟨reset_cert_a_1026, ⟨reset_cert_a_1027, ⟨reset_cert_a_1028, ⟨reset_cert_a_1029, ⟨reset_cert_a_1030, ⟨reset_cert_a_1031, ⟨reset_cert_a_1032, ⟨reset_cert_a_1033, ⟨reset_cert_a_1034, ⟨reset_cert_a_1035, ⟨reset_cert_a_1036, ⟨reset_cert_a_1037, ⟨reset_cert_a_1038, reset_cert_a_1039⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal

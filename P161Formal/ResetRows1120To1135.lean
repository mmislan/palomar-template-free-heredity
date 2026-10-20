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

theorem reset_cert_a_1120 : resetParentTest 1120 = true := by
  decide

theorem reset_cert_a_1121 : resetParentTest 1121 = true := by
  decide

theorem reset_cert_a_1122 : resetParentTest 1122 = true := by
  decide

theorem reset_cert_a_1123 : resetParentTest 1123 = true := by
  decide

theorem reset_cert_a_1124 : resetParentTest 1124 = true := by
  decide

theorem reset_cert_a_1125 : resetParentTest 1125 = true := by
  decide

theorem reset_cert_a_1126 : resetParentTest 1126 = true := by
  decide

theorem reset_cert_a_1127 : resetParentTest 1127 = true := by
  decide

theorem reset_cert_a_1128 : resetParentTest 1128 = true := by
  decide

theorem reset_cert_a_1129 : resetParentTest 1129 = true := by
  decide

theorem reset_cert_a_1130 : resetParentTest 1130 = true := by
  decide

theorem reset_cert_a_1131 : resetParentTest 1131 = true := by
  decide

theorem reset_cert_a_1132 : resetParentTest 1132 = true := by
  decide

theorem reset_cert_a_1133 : resetParentTest 1133 = true := by
  decide

theorem reset_cert_a_1134 : resetParentTest 1134 = true := by
  decide

theorem reset_cert_a_1135 : resetParentTest 1135 = true := by
  decide

def resetParents1120To1135 : List ℕ := [1120, 1121, 1122, 1123, 1124, 1125, 1126, 1127, 1128, 1129, 1130, 1131, 1132, 1133, 1134, 1135]

theorem reset_block_1120_to_1135 : resetParents1120To1135.all resetParentTest = true := by
  simp only [resetParents1120To1135, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1120, ⟨reset_cert_a_1121, ⟨reset_cert_a_1122, ⟨reset_cert_a_1123, ⟨reset_cert_a_1124, ⟨reset_cert_a_1125, ⟨reset_cert_a_1126, ⟨reset_cert_a_1127, ⟨reset_cert_a_1128, ⟨reset_cert_a_1129, ⟨reset_cert_a_1130, ⟨reset_cert_a_1131, ⟨reset_cert_a_1132, ⟨reset_cert_a_1133, ⟨reset_cert_a_1134, reset_cert_a_1135⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal

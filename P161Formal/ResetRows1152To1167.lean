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

theorem reset_cert_a_1152 : resetParentTest 1152 = true := by
  decide

theorem reset_cert_a_1153 : resetParentTest 1153 = true := by
  decide

theorem reset_cert_a_1154 : resetParentTest 1154 = true := by
  decide

theorem reset_cert_a_1155 : resetParentTest 1155 = true := by
  decide

theorem reset_cert_a_1156 : resetParentTest 1156 = true := by
  decide

theorem reset_cert_a_1157 : resetParentTest 1157 = true := by
  decide

theorem reset_cert_a_1158 : resetParentTest 1158 = true := by
  decide

theorem reset_cert_a_1159 : resetParentTest 1159 = true := by
  decide

theorem reset_cert_a_1160 : resetParentTest 1160 = true := by
  decide

theorem reset_cert_a_1161 : resetParentTest 1161 = true := by
  decide

theorem reset_cert_a_1162 : resetParentTest 1162 = true := by
  decide

theorem reset_cert_a_1163 : resetParentTest 1163 = true := by
  decide

theorem reset_cert_a_1164 : resetParentTest 1164 = true := by
  decide

theorem reset_cert_a_1165 : resetParentTest 1165 = true := by
  decide

theorem reset_cert_a_1166 : resetParentTest 1166 = true := by
  decide

theorem reset_cert_a_1167 : resetParentTest 1167 = true := by
  decide

def resetParents1152To1167 : List ℕ := [1152, 1153, 1154, 1155, 1156, 1157, 1158, 1159, 1160, 1161, 1162, 1163, 1164, 1165, 1166, 1167]

theorem reset_block_1152_to_1167 : resetParents1152To1167.all resetParentTest = true := by
  simp only [resetParents1152To1167, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1152, ⟨reset_cert_a_1153, ⟨reset_cert_a_1154, ⟨reset_cert_a_1155, ⟨reset_cert_a_1156, ⟨reset_cert_a_1157, ⟨reset_cert_a_1158, ⟨reset_cert_a_1159, ⟨reset_cert_a_1160, ⟨reset_cert_a_1161, ⟨reset_cert_a_1162, ⟨reset_cert_a_1163, ⟨reset_cert_a_1164, ⟨reset_cert_a_1165, ⟨reset_cert_a_1166, reset_cert_a_1167⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal

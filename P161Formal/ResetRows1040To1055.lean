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

theorem reset_cert_a_1040 : resetParentTest 1040 = true := by
  decide

theorem reset_cert_a_1041 : resetParentTest 1041 = true := by
  decide

theorem reset_cert_a_1042 : resetParentTest 1042 = true := by
  decide

theorem reset_cert_a_1043 : resetParentTest 1043 = true := by
  decide

theorem reset_cert_a_1044 : resetParentTest 1044 = true := by
  decide

theorem reset_cert_a_1045 : resetParentTest 1045 = true := by
  decide

theorem reset_cert_a_1046 : resetParentTest 1046 = true := by
  decide

theorem reset_cert_a_1047 : resetParentTest 1047 = true := by
  decide

theorem reset_cert_a_1048 : resetParentTest 1048 = true := by
  decide

theorem reset_cert_a_1049 : resetParentTest 1049 = true := by
  decide

theorem reset_cert_a_1050 : resetParentTest 1050 = true := by
  decide

theorem reset_cert_a_1051 : resetParentTest 1051 = true := by
  decide

theorem reset_cert_a_1052 : resetParentTest 1052 = true := by
  decide

theorem reset_cert_a_1053 : resetParentTest 1053 = true := by
  decide

theorem reset_cert_a_1054 : resetParentTest 1054 = true := by
  decide

theorem reset_cert_a_1055 : resetParentTest 1055 = true := by
  decide

def resetParents1040To1055 : List ℕ := [1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047, 1048, 1049, 1050, 1051, 1052, 1053, 1054, 1055]

theorem reset_block_1040_to_1055 : resetParents1040To1055.all resetParentTest = true := by
  simp only [resetParents1040To1055, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1040, ⟨reset_cert_a_1041, ⟨reset_cert_a_1042, ⟨reset_cert_a_1043, ⟨reset_cert_a_1044, ⟨reset_cert_a_1045, ⟨reset_cert_a_1046, ⟨reset_cert_a_1047, ⟨reset_cert_a_1048, ⟨reset_cert_a_1049, ⟨reset_cert_a_1050, ⟨reset_cert_a_1051, ⟨reset_cert_a_1052, ⟨reset_cert_a_1053, ⟨reset_cert_a_1054, reset_cert_a_1055⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal

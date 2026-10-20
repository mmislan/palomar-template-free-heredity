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

theorem reset_cert_a_112 : resetParentTest 112 = true := by
  decide

theorem reset_cert_a_113 : resetParentTest 113 = true := by
  decide

theorem reset_cert_a_114 : resetParentTest 114 = true := by
  decide

theorem reset_cert_a_115 : resetParentTest 115 = true := by
  decide

theorem reset_cert_a_116 : resetParentTest 116 = true := by
  decide

theorem reset_cert_a_117 : resetParentTest 117 = true := by
  decide

theorem reset_cert_a_118 : resetParentTest 118 = true := by
  decide

theorem reset_cert_a_119 : resetParentTest 119 = true := by
  decide

theorem reset_cert_a_120 : resetParentTest 120 = true := by
  decide

theorem reset_cert_a_121 : resetParentTest 121 = true := by
  decide

theorem reset_cert_a_122 : resetParentTest 122 = true := by
  decide

theorem reset_cert_a_123 : resetParentTest 123 = true := by
  decide

theorem reset_cert_a_124 : resetParentTest 124 = true := by
  decide

theorem reset_cert_a_125 : resetParentTest 125 = true := by
  decide

theorem reset_cert_a_126 : resetParentTest 126 = true := by
  decide

theorem reset_cert_a_127 : resetParentTest 127 = true := by
  decide

def resetParents112To127 : List ℕ := [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]

theorem reset_block_112_to_127 : resetParents112To127.all resetParentTest = true := by
  simp only [resetParents112To127, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_112, ⟨reset_cert_a_113, ⟨reset_cert_a_114, ⟨reset_cert_a_115, ⟨reset_cert_a_116, ⟨reset_cert_a_117, ⟨reset_cert_a_118, ⟨reset_cert_a_119, ⟨reset_cert_a_120, ⟨reset_cert_a_121, ⟨reset_cert_a_122, ⟨reset_cert_a_123, ⟨reset_cert_a_124, ⟨reset_cert_a_125, ⟨reset_cert_a_126, reset_cert_a_127⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal

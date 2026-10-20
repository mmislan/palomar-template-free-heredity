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

theorem reset_cert_a_128 : resetParentTest 128 = true := by
  decide

theorem reset_cert_a_129 : resetParentTest 129 = true := by
  decide

theorem reset_cert_a_130 : resetParentTest 130 = true := by
  decide

theorem reset_cert_a_131 : resetParentTest 131 = true := by
  decide

theorem reset_cert_a_132 : resetParentTest 132 = true := by
  decide

theorem reset_cert_a_133 : resetParentTest 133 = true := by
  decide

theorem reset_cert_a_134 : resetParentTest 134 = true := by
  decide

theorem reset_cert_a_135 : resetParentTest 135 = true := by
  decide

theorem reset_cert_a_136 : resetParentTest 136 = true := by
  decide

theorem reset_cert_a_137 : resetParentTest 137 = true := by
  decide

theorem reset_cert_a_138 : resetParentTest 138 = true := by
  decide

theorem reset_cert_a_139 : resetParentTest 139 = true := by
  decide

theorem reset_cert_a_140 : resetParentTest 140 = true := by
  decide

theorem reset_cert_a_141 : resetParentTest 141 = true := by
  decide

theorem reset_cert_a_142 : resetParentTest 142 = true := by
  decide

theorem reset_cert_a_143 : resetParentTest 143 = true := by
  decide

def resetParents128To143 : List ℕ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]

theorem reset_block_128_to_143 : resetParents128To143.all resetParentTest = true := by
  simp only [resetParents128To143, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_128, ⟨reset_cert_a_129, ⟨reset_cert_a_130, ⟨reset_cert_a_131, ⟨reset_cert_a_132, ⟨reset_cert_a_133, ⟨reset_cert_a_134, ⟨reset_cert_a_135, ⟨reset_cert_a_136, ⟨reset_cert_a_137, ⟨reset_cert_a_138, ⟨reset_cert_a_139, ⟨reset_cert_a_140, ⟨reset_cert_a_141, ⟨reset_cert_a_142, reset_cert_a_143⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal

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

theorem reset_cert_a_176 : resetParentTest 176 = true := by
  decide

theorem reset_cert_a_177 : resetParentTest 177 = true := by
  decide

theorem reset_cert_a_178 : resetParentTest 178 = true := by
  decide

theorem reset_cert_a_179 : resetParentTest 179 = true := by
  decide

theorem reset_cert_a_180 : resetParentTest 180 = true := by
  decide

theorem reset_cert_a_181 : resetParentTest 181 = true := by
  decide

theorem reset_cert_a_182 : resetParentTest 182 = true := by
  decide

theorem reset_cert_a_183 : resetParentTest 183 = true := by
  decide

theorem reset_cert_a_184 : resetParentTest 184 = true := by
  decide

theorem reset_cert_a_185 : resetParentTest 185 = true := by
  decide

theorem reset_cert_a_186 : resetParentTest 186 = true := by
  decide

theorem reset_cert_a_187 : resetParentTest 187 = true := by
  decide

theorem reset_cert_a_188 : resetParentTest 188 = true := by
  decide

theorem reset_cert_a_189 : resetParentTest 189 = true := by
  decide

theorem reset_cert_a_190 : resetParentTest 190 = true := by
  decide

theorem reset_cert_a_191 : resetParentTest 191 = true := by
  decide

def resetParents176To191 : List ℕ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]

theorem reset_block_176_to_191 : resetParents176To191.all resetParentTest = true := by
  simp only [resetParents176To191, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_176, ⟨reset_cert_a_177, ⟨reset_cert_a_178, ⟨reset_cert_a_179, ⟨reset_cert_a_180, ⟨reset_cert_a_181, ⟨reset_cert_a_182, ⟨reset_cert_a_183, ⟨reset_cert_a_184, ⟨reset_cert_a_185, ⟨reset_cert_a_186, ⟨reset_cert_a_187, ⟨reset_cert_a_188, ⟨reset_cert_a_189, ⟨reset_cert_a_190, reset_cert_a_191⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal

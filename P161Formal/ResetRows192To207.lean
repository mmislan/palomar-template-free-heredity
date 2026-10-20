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

theorem reset_cert_a_192 : resetParentTest 192 = true := by
  decide

theorem reset_cert_a_193 : resetParentTest 193 = true := by
  decide

theorem reset_cert_a_194 : resetParentTest 194 = true := by
  decide

theorem reset_cert_a_195 : resetParentTest 195 = true := by
  decide

theorem reset_cert_a_196 : resetParentTest 196 = true := by
  decide

theorem reset_cert_a_197 : resetParentTest 197 = true := by
  decide

theorem reset_cert_a_198 : resetParentTest 198 = true := by
  decide

theorem reset_cert_a_199 : resetParentTest 199 = true := by
  decide

theorem reset_cert_a_200 : resetParentTest 200 = true := by
  decide

theorem reset_cert_a_201 : resetParentTest 201 = true := by
  decide

theorem reset_cert_a_202 : resetParentTest 202 = true := by
  decide

theorem reset_cert_a_203 : resetParentTest 203 = true := by
  decide

theorem reset_cert_a_204 : resetParentTest 204 = true := by
  decide

theorem reset_cert_a_205 : resetParentTest 205 = true := by
  decide

theorem reset_cert_a_206 : resetParentTest 206 = true := by
  decide

theorem reset_cert_a_207 : resetParentTest 207 = true := by
  decide

def resetParents192To207 : List ℕ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]

theorem reset_block_192_to_207 : resetParents192To207.all resetParentTest = true := by
  simp only [resetParents192To207, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_192, ⟨reset_cert_a_193, ⟨reset_cert_a_194, ⟨reset_cert_a_195, ⟨reset_cert_a_196, ⟨reset_cert_a_197, ⟨reset_cert_a_198, ⟨reset_cert_a_199, ⟨reset_cert_a_200, ⟨reset_cert_a_201, ⟨reset_cert_a_202, ⟨reset_cert_a_203, ⟨reset_cert_a_204, ⟨reset_cert_a_205, ⟨reset_cert_a_206, reset_cert_a_207⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal

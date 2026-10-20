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

theorem reset_cert_a_208 : resetParentTest 208 = true := by
  decide

theorem reset_cert_a_209 : resetParentTest 209 = true := by
  decide

theorem reset_cert_a_210 : resetParentTest 210 = true := by
  decide

theorem reset_cert_a_211 : resetParentTest 211 = true := by
  decide

theorem reset_cert_a_212 : resetParentTest 212 = true := by
  decide

theorem reset_cert_a_213 : resetParentTest 213 = true := by
  decide

theorem reset_cert_a_214 : resetParentTest 214 = true := by
  decide

theorem reset_cert_a_215 : resetParentTest 215 = true := by
  decide

theorem reset_cert_a_216 : resetParentTest 216 = true := by
  decide

theorem reset_cert_a_217 : resetParentTest 217 = true := by
  decide

theorem reset_cert_a_218 : resetParentTest 218 = true := by
  decide

theorem reset_cert_a_219 : resetParentTest 219 = true := by
  decide

theorem reset_cert_a_220 : resetParentTest 220 = true := by
  decide

theorem reset_cert_a_221 : resetParentTest 221 = true := by
  decide

theorem reset_cert_a_222 : resetParentTest 222 = true := by
  decide

theorem reset_cert_a_223 : resetParentTest 223 = true := by
  decide

def resetParents208To223 : List ℕ := [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]

theorem reset_block_208_to_223 : resetParents208To223.all resetParentTest = true := by
  simp only [resetParents208To223, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_208, ⟨reset_cert_a_209, ⟨reset_cert_a_210, ⟨reset_cert_a_211, ⟨reset_cert_a_212, ⟨reset_cert_a_213, ⟨reset_cert_a_214, ⟨reset_cert_a_215, ⟨reset_cert_a_216, ⟨reset_cert_a_217, ⟨reset_cert_a_218, ⟨reset_cert_a_219, ⟨reset_cert_a_220, ⟨reset_cert_a_221, ⟨reset_cert_a_222, reset_cert_a_223⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal

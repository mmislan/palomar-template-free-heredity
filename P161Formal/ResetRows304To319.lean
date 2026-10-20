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

theorem reset_cert_a_304 : resetParentTest 304 = true := by
  decide

theorem reset_cert_a_305 : resetParentTest 305 = true := by
  decide

theorem reset_cert_a_306 : resetParentTest 306 = true := by
  decide

theorem reset_cert_a_307 : resetParentTest 307 = true := by
  decide

theorem reset_cert_a_308 : resetParentTest 308 = true := by
  decide

theorem reset_cert_a_309 : resetParentTest 309 = true := by
  decide

theorem reset_cert_a_310 : resetParentTest 310 = true := by
  decide

theorem reset_cert_a_311 : resetParentTest 311 = true := by
  decide

theorem reset_cert_a_312 : resetParentTest 312 = true := by
  decide

theorem reset_cert_a_313 : resetParentTest 313 = true := by
  decide

theorem reset_cert_a_314 : resetParentTest 314 = true := by
  decide

theorem reset_cert_a_315 : resetParentTest 315 = true := by
  decide

theorem reset_cert_a_316 : resetParentTest 316 = true := by
  decide

theorem reset_cert_a_317 : resetParentTest 317 = true := by
  decide

theorem reset_cert_a_318 : resetParentTest 318 = true := by
  decide

theorem reset_cert_a_319 : resetParentTest 319 = true := by
  decide

def resetParents304To319 : List ℕ := [304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319]

theorem reset_block_304_to_319 : resetParents304To319.all resetParentTest = true := by
  simp only [resetParents304To319, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_304, ⟨reset_cert_a_305, ⟨reset_cert_a_306, ⟨reset_cert_a_307, ⟨reset_cert_a_308, ⟨reset_cert_a_309, ⟨reset_cert_a_310, ⟨reset_cert_a_311, ⟨reset_cert_a_312, ⟨reset_cert_a_313, ⟨reset_cert_a_314, ⟨reset_cert_a_315, ⟨reset_cert_a_316, ⟨reset_cert_a_317, ⟨reset_cert_a_318, reset_cert_a_319⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal

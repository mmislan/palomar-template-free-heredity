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

theorem reset_cert_a_288 : resetParentTest 288 = true := by
  decide

theorem reset_cert_a_289 : resetParentTest 289 = true := by
  decide

theorem reset_cert_a_290 : resetParentTest 290 = true := by
  decide

theorem reset_cert_a_291 : resetParentTest 291 = true := by
  decide

theorem reset_cert_a_292 : resetParentTest 292 = true := by
  decide

theorem reset_cert_a_293 : resetParentTest 293 = true := by
  decide

theorem reset_cert_a_294 : resetParentTest 294 = true := by
  decide

theorem reset_cert_a_295 : resetParentTest 295 = true := by
  decide

theorem reset_cert_a_296 : resetParentTest 296 = true := by
  decide

theorem reset_cert_a_297 : resetParentTest 297 = true := by
  decide

theorem reset_cert_a_298 : resetParentTest 298 = true := by
  decide

theorem reset_cert_a_299 : resetParentTest 299 = true := by
  decide

theorem reset_cert_a_300 : resetParentTest 300 = true := by
  decide

theorem reset_cert_a_301 : resetParentTest 301 = true := by
  decide

theorem reset_cert_a_302 : resetParentTest 302 = true := by
  decide

theorem reset_cert_a_303 : resetParentTest 303 = true := by
  decide

def resetParents288To303 : List ℕ := [288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303]

theorem reset_block_288_to_303 : resetParents288To303.all resetParentTest = true := by
  simp only [resetParents288To303, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_288, ⟨reset_cert_a_289, ⟨reset_cert_a_290, ⟨reset_cert_a_291, ⟨reset_cert_a_292, ⟨reset_cert_a_293, ⟨reset_cert_a_294, ⟨reset_cert_a_295, ⟨reset_cert_a_296, ⟨reset_cert_a_297, ⟨reset_cert_a_298, ⟨reset_cert_a_299, ⟨reset_cert_a_300, ⟨reset_cert_a_301, ⟨reset_cert_a_302, reset_cert_a_303⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal

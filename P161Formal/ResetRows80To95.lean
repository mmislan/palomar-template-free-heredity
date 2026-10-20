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

theorem reset_cert_a_80 : resetParentTest 80 = true := by
  decide

theorem reset_cert_a_81 : resetParentTest 81 = true := by
  decide

theorem reset_cert_a_82 : resetParentTest 82 = true := by
  decide

theorem reset_cert_a_83 : resetParentTest 83 = true := by
  decide

theorem reset_cert_a_84 : resetParentTest 84 = true := by
  decide

theorem reset_cert_a_85 : resetParentTest 85 = true := by
  decide

theorem reset_cert_a_86 : resetParentTest 86 = true := by
  decide

theorem reset_cert_a_87 : resetParentTest 87 = true := by
  decide

theorem reset_cert_a_88 : resetParentTest 88 = true := by
  decide

theorem reset_cert_a_89 : resetParentTest 89 = true := by
  decide

theorem reset_cert_a_90 : resetParentTest 90 = true := by
  decide

theorem reset_cert_a_91 : resetParentTest 91 = true := by
  decide

theorem reset_cert_a_92 : resetParentTest 92 = true := by
  decide

theorem reset_cert_a_93 : resetParentTest 93 = true := by
  decide

theorem reset_cert_a_94 : resetParentTest 94 = true := by
  decide

theorem reset_cert_a_95 : resetParentTest 95 = true := by
  decide

def resetParents80To95 : List ℕ := [80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]

theorem reset_block_80_to_95 : resetParents80To95.all resetParentTest = true := by
  simp only [resetParents80To95, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_80, ⟨reset_cert_a_81, ⟨reset_cert_a_82, ⟨reset_cert_a_83, ⟨reset_cert_a_84, ⟨reset_cert_a_85, ⟨reset_cert_a_86, ⟨reset_cert_a_87, ⟨reset_cert_a_88, ⟨reset_cert_a_89, ⟨reset_cert_a_90, ⟨reset_cert_a_91, ⟨reset_cert_a_92, ⟨reset_cert_a_93, ⟨reset_cert_a_94, reset_cert_a_95⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal

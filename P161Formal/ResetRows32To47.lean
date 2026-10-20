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

theorem reset_cert_a_32 : resetParentTest 32 = true := by
  obtain ⟨g0, g1, d0, d1⟩ := reset_row32_pilot
  simp [resetParentTest, g0, g1, d0, d1]

theorem reset_cert_a_33 : resetParentTest 33 = true := by
  decide

theorem reset_cert_a_34 : resetParentTest 34 = true := by
  decide

theorem reset_cert_a_35 : resetParentTest 35 = true := by
  decide

theorem reset_cert_a_36 : resetParentTest 36 = true := by
  decide

theorem reset_cert_a_37 : resetParentTest 37 = true := by
  decide

theorem reset_cert_a_38 : resetParentTest 38 = true := by
  decide

theorem reset_cert_a_39 : resetParentTest 39 = true := by
  decide

theorem reset_cert_a_40 : resetParentTest 40 = true := by
  decide

theorem reset_cert_a_41 : resetParentTest 41 = true := by
  decide

theorem reset_cert_a_42 : resetParentTest 42 = true := by
  decide

theorem reset_cert_a_43 : resetParentTest 43 = true := by
  decide

theorem reset_cert_a_44 : resetParentTest 44 = true := by
  decide

theorem reset_cert_a_45 : resetParentTest 45 = true := by
  decide

theorem reset_cert_a_46 : resetParentTest 46 = true := by
  decide

theorem reset_cert_a_47 : resetParentTest 47 = true := by
  decide

def resetParents32To47 : List ℕ := [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]

theorem reset_block_32_to_47 : resetParents32To47.all resetParentTest = true := by
  simp only [resetParents32To47, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_32, ⟨reset_cert_a_33, ⟨reset_cert_a_34, ⟨reset_cert_a_35, ⟨reset_cert_a_36, ⟨reset_cert_a_37, ⟨reset_cert_a_38, ⟨reset_cert_a_39, ⟨reset_cert_a_40, ⟨reset_cert_a_41, ⟨reset_cert_a_42, ⟨reset_cert_a_43, ⟨reset_cert_a_44, ⟨reset_cert_a_45, ⟨reset_cert_a_46, reset_cert_a_47⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal

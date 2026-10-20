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

theorem reset_cert_a_1008 : resetParentTest 1008 = true := by
  decide

theorem reset_cert_a_1009 : resetParentTest 1009 = true := by
  decide

theorem reset_cert_a_1010 : resetParentTest 1010 = true := by
  decide

theorem reset_cert_a_1011 : resetParentTest 1011 = true := by
  decide

theorem reset_cert_a_1012 : resetParentTest 1012 = true := by
  decide

theorem reset_cert_a_1013 : resetParentTest 1013 = true := by
  decide

theorem reset_cert_a_1014 : resetParentTest 1014 = true := by
  decide

theorem reset_cert_a_1015 : resetParentTest 1015 = true := by
  decide

theorem reset_cert_a_1016 : resetParentTest 1016 = true := by
  decide

theorem reset_cert_a_1017 : resetParentTest 1017 = true := by
  decide

theorem reset_cert_a_1018 : resetParentTest 1018 = true := by
  decide

theorem reset_cert_a_1019 : resetParentTest 1019 = true := by
  decide

theorem reset_cert_a_1020 : resetParentTest 1020 = true := by
  decide

theorem reset_cert_a_1021 : resetParentTest 1021 = true := by
  decide

theorem reset_cert_a_1022 : resetParentTest 1022 = true := by
  decide

theorem reset_cert_a_1023 : resetParentTest 1023 = true := by
  decide

def resetParents1008To1023 : List ℕ := [1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]

theorem reset_block_1008_to_1023 : resetParents1008To1023.all resetParentTest = true := by
  simp only [resetParents1008To1023, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1008, ⟨reset_cert_a_1009, ⟨reset_cert_a_1010, ⟨reset_cert_a_1011, ⟨reset_cert_a_1012, ⟨reset_cert_a_1013, ⟨reset_cert_a_1014, ⟨reset_cert_a_1015, ⟨reset_cert_a_1016, ⟨reset_cert_a_1017, ⟨reset_cert_a_1018, ⟨reset_cert_a_1019, ⟨reset_cert_a_1020, ⟨reset_cert_a_1021, ⟨reset_cert_a_1022, reset_cert_a_1023⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal

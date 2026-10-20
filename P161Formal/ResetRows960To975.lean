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

theorem reset_cert_a_960 : resetParentTest 960 = true := by
  decide

theorem reset_cert_a_961 : resetParentTest 961 = true := by
  decide

theorem reset_cert_a_962 : resetParentTest 962 = true := by
  decide

theorem reset_cert_a_963 : resetParentTest 963 = true := by
  decide

theorem reset_cert_a_964 : resetParentTest 964 = true := by
  decide

theorem reset_cert_a_965 : resetParentTest 965 = true := by
  decide

theorem reset_cert_a_966 : resetParentTest 966 = true := by
  decide

theorem reset_cert_a_967 : resetParentTest 967 = true := by
  decide

theorem reset_cert_a_968 : resetParentTest 968 = true := by
  decide

theorem reset_cert_a_969 : resetParentTest 969 = true := by
  decide

theorem reset_cert_a_970 : resetParentTest 970 = true := by
  decide

theorem reset_cert_a_971 : resetParentTest 971 = true := by
  decide

theorem reset_cert_a_972 : resetParentTest 972 = true := by
  decide

theorem reset_cert_a_973 : resetParentTest 973 = true := by
  decide

theorem reset_cert_a_974 : resetParentTest 974 = true := by
  decide

theorem reset_cert_a_975 : resetParentTest 975 = true := by
  decide

def resetParents960To975 : List ℕ := [960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975]

theorem reset_block_960_to_975 : resetParents960To975.all resetParentTest = true := by
  simp only [resetParents960To975, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_960, ⟨reset_cert_a_961, ⟨reset_cert_a_962, ⟨reset_cert_a_963, ⟨reset_cert_a_964, ⟨reset_cert_a_965, ⟨reset_cert_a_966, ⟨reset_cert_a_967, ⟨reset_cert_a_968, ⟨reset_cert_a_969, ⟨reset_cert_a_970, ⟨reset_cert_a_971, ⟨reset_cert_a_972, ⟨reset_cert_a_973, ⟨reset_cert_a_974, reset_cert_a_975⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal

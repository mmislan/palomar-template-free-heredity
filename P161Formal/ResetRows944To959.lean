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

theorem reset_cert_a_944 : resetParentTest 944 = true := by
  decide

theorem reset_cert_a_945 : resetParentTest 945 = true := by
  decide

theorem reset_cert_a_946 : resetParentTest 946 = true := by
  decide

theorem reset_cert_a_947 : resetParentTest 947 = true := by
  decide

theorem reset_cert_a_948 : resetParentTest 948 = true := by
  decide

theorem reset_cert_a_949 : resetParentTest 949 = true := by
  decide

theorem reset_cert_a_950 : resetParentTest 950 = true := by
  decide

theorem reset_cert_a_951 : resetParentTest 951 = true := by
  decide

theorem reset_cert_a_952 : resetParentTest 952 = true := by
  decide

theorem reset_cert_a_953 : resetParentTest 953 = true := by
  decide

theorem reset_cert_a_954 : resetParentTest 954 = true := by
  decide

theorem reset_cert_a_955 : resetParentTest 955 = true := by
  decide

theorem reset_cert_a_956 : resetParentTest 956 = true := by
  decide

theorem reset_cert_a_957 : resetParentTest 957 = true := by
  decide

theorem reset_cert_a_958 : resetParentTest 958 = true := by
  decide

theorem reset_cert_a_959 : resetParentTest 959 = true := by
  decide

def resetParents944To959 : List ℕ := [944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959]

theorem reset_block_944_to_959 : resetParents944To959.all resetParentTest = true := by
  simp only [resetParents944To959, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_944, ⟨reset_cert_a_945, ⟨reset_cert_a_946, ⟨reset_cert_a_947, ⟨reset_cert_a_948, ⟨reset_cert_a_949, ⟨reset_cert_a_950, ⟨reset_cert_a_951, ⟨reset_cert_a_952, ⟨reset_cert_a_953, ⟨reset_cert_a_954, ⟨reset_cert_a_955, ⟨reset_cert_a_956, ⟨reset_cert_a_957, ⟨reset_cert_a_958, reset_cert_a_959⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal

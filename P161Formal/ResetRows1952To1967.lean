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

theorem reset_cert_a_1952 : resetParentTest 1952 = true := by
  decide

theorem reset_cert_a_1953 : resetParentTest 1953 = true := by
  decide

theorem reset_cert_a_1954 : resetParentTest 1954 = true := by
  decide

theorem reset_cert_a_1955 : resetParentTest 1955 = true := by
  decide

theorem reset_cert_a_1956 : resetParentTest 1956 = true := by
  decide

theorem reset_cert_a_1957 : resetParentTest 1957 = true := by
  decide

theorem reset_cert_a_1958 : resetParentTest 1958 = true := by
  decide

theorem reset_cert_a_1959 : resetParentTest 1959 = true := by
  decide

theorem reset_cert_a_1960 : resetParentTest 1960 = true := by
  decide

theorem reset_cert_a_1961 : resetParentTest 1961 = true := by
  decide

theorem reset_cert_a_1962 : resetParentTest 1962 = true := by
  decide

theorem reset_cert_a_1963 : resetParentTest 1963 = true := by
  decide

theorem reset_cert_a_1964 : resetParentTest 1964 = true := by
  decide

theorem reset_cert_a_1965 : resetParentTest 1965 = true := by
  decide

theorem reset_cert_a_1966 : resetParentTest 1966 = true := by
  decide

theorem reset_cert_a_1967 : resetParentTest 1967 = true := by
  decide

def resetParents1952To1967 : List ℕ := [1952, 1953, 1954, 1955, 1956, 1957, 1958, 1959, 1960, 1961, 1962, 1963, 1964, 1965, 1966, 1967]

theorem reset_block_1952_to_1967 : resetParents1952To1967.all resetParentTest = true := by
  simp only [resetParents1952To1967, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1952, ⟨reset_cert_a_1953, ⟨reset_cert_a_1954, ⟨reset_cert_a_1955, ⟨reset_cert_a_1956, ⟨reset_cert_a_1957, ⟨reset_cert_a_1958, ⟨reset_cert_a_1959, ⟨reset_cert_a_1960, ⟨reset_cert_a_1961, ⟨reset_cert_a_1962, ⟨reset_cert_a_1963, ⟨reset_cert_a_1964, ⟨reset_cert_a_1965, ⟨reset_cert_a_1966, reset_cert_a_1967⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal

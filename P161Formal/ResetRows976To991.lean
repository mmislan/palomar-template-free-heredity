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

theorem reset_cert_a_976 : resetParentTest 976 = true := by
  decide

theorem reset_cert_a_977 : resetParentTest 977 = true := by
  decide

theorem reset_cert_a_978 : resetParentTest 978 = true := by
  decide

theorem reset_cert_a_979 : resetParentTest 979 = true := by
  decide

theorem reset_cert_a_980 : resetParentTest 980 = true := by
  decide

theorem reset_cert_a_981 : resetParentTest 981 = true := by
  decide

theorem reset_cert_a_982 : resetParentTest 982 = true := by
  decide

theorem reset_cert_a_983 : resetParentTest 983 = true := by
  decide

theorem reset_cert_a_984 : resetParentTest 984 = true := by
  decide

theorem reset_cert_a_985 : resetParentTest 985 = true := by
  decide

theorem reset_cert_a_986 : resetParentTest 986 = true := by
  decide

theorem reset_cert_a_987 : resetParentTest 987 = true := by
  decide

theorem reset_cert_a_988 : resetParentTest 988 = true := by
  decide

theorem reset_cert_a_989 : resetParentTest 989 = true := by
  decide

theorem reset_cert_a_990 : resetParentTest 990 = true := by
  decide

theorem reset_cert_a_991 : resetParentTest 991 = true := by
  decide

def resetParents976To991 : List ℕ := [976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991]

theorem reset_block_976_to_991 : resetParents976To991.all resetParentTest = true := by
  simp only [resetParents976To991, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_976, ⟨reset_cert_a_977, ⟨reset_cert_a_978, ⟨reset_cert_a_979, ⟨reset_cert_a_980, ⟨reset_cert_a_981, ⟨reset_cert_a_982, ⟨reset_cert_a_983, ⟨reset_cert_a_984, ⟨reset_cert_a_985, ⟨reset_cert_a_986, ⟨reset_cert_a_987, ⟨reset_cert_a_988, ⟨reset_cert_a_989, ⟨reset_cert_a_990, reset_cert_a_991⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal

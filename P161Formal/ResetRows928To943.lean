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

theorem reset_cert_a_928 : resetParentTest 928 = true := by
  decide

theorem reset_cert_a_929 : resetParentTest 929 = true := by
  decide

theorem reset_cert_a_930 : resetParentTest 930 = true := by
  decide

theorem reset_cert_a_931 : resetParentTest 931 = true := by
  decide

theorem reset_cert_a_932 : resetParentTest 932 = true := by
  decide

theorem reset_cert_a_933 : resetParentTest 933 = true := by
  decide

theorem reset_cert_a_934 : resetParentTest 934 = true := by
  decide

theorem reset_cert_a_935 : resetParentTest 935 = true := by
  decide

theorem reset_cert_a_936 : resetParentTest 936 = true := by
  decide

theorem reset_cert_a_937 : resetParentTest 937 = true := by
  decide

theorem reset_cert_a_938 : resetParentTest 938 = true := by
  decide

theorem reset_cert_a_939 : resetParentTest 939 = true := by
  decide

theorem reset_cert_a_940 : resetParentTest 940 = true := by
  decide

theorem reset_cert_a_941 : resetParentTest 941 = true := by
  decide

theorem reset_cert_a_942 : resetParentTest 942 = true := by
  decide

theorem reset_cert_a_943 : resetParentTest 943 = true := by
  decide

def resetParents928To943 : List ℕ := [928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943]

theorem reset_block_928_to_943 : resetParents928To943.all resetParentTest = true := by
  simp only [resetParents928To943, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_928, ⟨reset_cert_a_929, ⟨reset_cert_a_930, ⟨reset_cert_a_931, ⟨reset_cert_a_932, ⟨reset_cert_a_933, ⟨reset_cert_a_934, ⟨reset_cert_a_935, ⟨reset_cert_a_936, ⟨reset_cert_a_937, ⟨reset_cert_a_938, ⟨reset_cert_a_939, ⟨reset_cert_a_940, ⟨reset_cert_a_941, ⟨reset_cert_a_942, reset_cert_a_943⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal

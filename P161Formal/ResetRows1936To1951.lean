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

theorem reset_cert_a_1936 : resetParentTest 1936 = true := by
  decide

theorem reset_cert_a_1937 : resetParentTest 1937 = true := by
  decide

theorem reset_cert_a_1938 : resetParentTest 1938 = true := by
  decide

theorem reset_cert_a_1939 : resetParentTest 1939 = true := by
  decide

theorem reset_cert_a_1940 : resetParentTest 1940 = true := by
  decide

theorem reset_cert_a_1941 : resetParentTest 1941 = true := by
  decide

theorem reset_cert_a_1942 : resetParentTest 1942 = true := by
  decide

theorem reset_cert_a_1943 : resetParentTest 1943 = true := by
  decide

theorem reset_cert_a_1944 : resetParentTest 1944 = true := by
  decide

theorem reset_cert_a_1945 : resetParentTest 1945 = true := by
  decide

theorem reset_cert_a_1946 : resetParentTest 1946 = true := by
  decide

theorem reset_cert_a_1947 : resetParentTest 1947 = true := by
  decide

theorem reset_cert_a_1948 : resetParentTest 1948 = true := by
  decide

theorem reset_cert_a_1949 : resetParentTest 1949 = true := by
  decide

theorem reset_cert_a_1950 : resetParentTest 1950 = true := by
  decide

theorem reset_cert_a_1951 : resetParentTest 1951 = true := by
  decide

def resetParents1936To1951 : List ℕ := [1936, 1937, 1938, 1939, 1940, 1941, 1942, 1943, 1944, 1945, 1946, 1947, 1948, 1949, 1950, 1951]

theorem reset_block_1936_to_1951 : resetParents1936To1951.all resetParentTest = true := by
  simp only [resetParents1936To1951, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1936, ⟨reset_cert_a_1937, ⟨reset_cert_a_1938, ⟨reset_cert_a_1939, ⟨reset_cert_a_1940, ⟨reset_cert_a_1941, ⟨reset_cert_a_1942, ⟨reset_cert_a_1943, ⟨reset_cert_a_1944, ⟨reset_cert_a_1945, ⟨reset_cert_a_1946, ⟨reset_cert_a_1947, ⟨reset_cert_a_1948, ⟨reset_cert_a_1949, ⟨reset_cert_a_1950, reset_cert_a_1951⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal

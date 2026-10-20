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

theorem reset_cert_a_1920 : resetParentTest 1920 = true := by
  decide

theorem reset_cert_a_1921 : resetParentTest 1921 = true := by
  decide

theorem reset_cert_a_1922 : resetParentTest 1922 = true := by
  decide

theorem reset_cert_a_1923 : resetParentTest 1923 = true := by
  decide

theorem reset_cert_a_1924 : resetParentTest 1924 = true := by
  decide

theorem reset_cert_a_1925 : resetParentTest 1925 = true := by
  decide

theorem reset_cert_a_1926 : resetParentTest 1926 = true := by
  decide

theorem reset_cert_a_1927 : resetParentTest 1927 = true := by
  decide

theorem reset_cert_a_1928 : resetParentTest 1928 = true := by
  decide

theorem reset_cert_a_1929 : resetParentTest 1929 = true := by
  decide

theorem reset_cert_a_1930 : resetParentTest 1930 = true := by
  decide

theorem reset_cert_a_1931 : resetParentTest 1931 = true := by
  decide

theorem reset_cert_a_1932 : resetParentTest 1932 = true := by
  decide

theorem reset_cert_a_1933 : resetParentTest 1933 = true := by
  decide

theorem reset_cert_a_1934 : resetParentTest 1934 = true := by
  decide

theorem reset_cert_a_1935 : resetParentTest 1935 = true := by
  decide

def resetParents1920To1935 : List ℕ := [1920, 1921, 1922, 1923, 1924, 1925, 1926, 1927, 1928, 1929, 1930, 1931, 1932, 1933, 1934, 1935]

theorem reset_block_1920_to_1935 : resetParents1920To1935.all resetParentTest = true := by
  simp only [resetParents1920To1935, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1920, ⟨reset_cert_a_1921, ⟨reset_cert_a_1922, ⟨reset_cert_a_1923, ⟨reset_cert_a_1924, ⟨reset_cert_a_1925, ⟨reset_cert_a_1926, ⟨reset_cert_a_1927, ⟨reset_cert_a_1928, ⟨reset_cert_a_1929, ⟨reset_cert_a_1930, ⟨reset_cert_a_1931, ⟨reset_cert_a_1932, ⟨reset_cert_a_1933, ⟨reset_cert_a_1934, reset_cert_a_1935⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal

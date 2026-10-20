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

theorem reset_cert_a_1904 : resetParentTest 1904 = true := by
  decide

theorem reset_cert_a_1905 : resetParentTest 1905 = true := by
  decide

theorem reset_cert_a_1906 : resetParentTest 1906 = true := by
  decide

theorem reset_cert_a_1907 : resetParentTest 1907 = true := by
  decide

theorem reset_cert_a_1908 : resetParentTest 1908 = true := by
  decide

theorem reset_cert_a_1909 : resetParentTest 1909 = true := by
  decide

theorem reset_cert_a_1910 : resetParentTest 1910 = true := by
  decide

theorem reset_cert_a_1911 : resetParentTest 1911 = true := by
  decide

theorem reset_cert_a_1912 : resetParentTest 1912 = true := by
  decide

theorem reset_cert_a_1913 : resetParentTest 1913 = true := by
  decide

theorem reset_cert_a_1914 : resetParentTest 1914 = true := by
  decide

theorem reset_cert_a_1915 : resetParentTest 1915 = true := by
  decide

theorem reset_cert_a_1916 : resetParentTest 1916 = true := by
  decide

theorem reset_cert_a_1917 : resetParentTest 1917 = true := by
  decide

theorem reset_cert_a_1918 : resetParentTest 1918 = true := by
  decide

theorem reset_cert_a_1919 : resetParentTest 1919 = true := by
  decide

def resetParents1904To1919 : List ℕ := [1904, 1905, 1906, 1907, 1908, 1909, 1910, 1911, 1912, 1913, 1914, 1915, 1916, 1917, 1918, 1919]

theorem reset_block_1904_to_1919 : resetParents1904To1919.all resetParentTest = true := by
  simp only [resetParents1904To1919, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1904, ⟨reset_cert_a_1905, ⟨reset_cert_a_1906, ⟨reset_cert_a_1907, ⟨reset_cert_a_1908, ⟨reset_cert_a_1909, ⟨reset_cert_a_1910, ⟨reset_cert_a_1911, ⟨reset_cert_a_1912, ⟨reset_cert_a_1913, ⟨reset_cert_a_1914, ⟨reset_cert_a_1915, ⟨reset_cert_a_1916, ⟨reset_cert_a_1917, ⟨reset_cert_a_1918, reset_cert_a_1919⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal

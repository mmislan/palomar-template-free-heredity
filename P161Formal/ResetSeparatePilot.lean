module

public import P161Formal.ResetChecker

/-! Same16-parent cost pilot with a separate kernel reduction per parent.
The final block proof composes the checked rows without recomputing moments. -/

public section
namespace P161Formal

set_option maxRecDepth 32768 in
set_option maxHeartbeats 800000 in
set_option exponentiation.threshold 2048 in
theorem separate_reset_2033 :
    checkGlobalResetRow 2033 false = true ∧ checkGlobalResetRow 2033 true = true := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 800000 in
set_option exponentiation.threshold 2048 in
theorem separate_reset_2034 :
    checkGlobalResetRow 2034 false = true ∧ checkGlobalResetRow 2034 true = true := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 800000 in
set_option exponentiation.threshold 2048 in
theorem separate_reset_2035 :
    checkGlobalResetRow 2035 false = true ∧ checkGlobalResetRow 2035 true = true := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 800000 in
set_option exponentiation.threshold 2048 in
theorem separate_reset_2036 :
    checkGlobalResetRow 2036 false = true ∧ checkGlobalResetRow 2036 true = true := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 800000 in
set_option exponentiation.threshold 2048 in
theorem separate_reset_2037 :
    checkGlobalResetRow 2037 false = true ∧ checkGlobalResetRow 2037 true = true := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 800000 in
set_option exponentiation.threshold 2048 in
theorem separate_reset_2038 :
    checkGlobalResetRow 2038 false = true ∧ checkGlobalResetRow 2038 true = true := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 800000 in
set_option exponentiation.threshold 2048 in
theorem separate_reset_2039 :
    checkGlobalResetRow 2039 false = true ∧ checkGlobalResetRow 2039 true = true := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 800000 in
set_option exponentiation.threshold 2048 in
theorem separate_reset_2040 :
    checkGlobalResetRow 2040 false = true ∧ checkGlobalResetRow 2040 true = true := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 800000 in
set_option exponentiation.threshold 2048 in
theorem separate_reset_2041 :
    checkGlobalResetRow 2041 false = true ∧ checkGlobalResetRow 2041 true = true := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 800000 in
set_option exponentiation.threshold 2048 in
theorem separate_reset_2042 :
    checkGlobalResetRow 2042 false = true ∧ checkGlobalResetRow 2042 true = true := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 800000 in
set_option exponentiation.threshold 2048 in
theorem separate_reset_2043 :
    checkGlobalResetRow 2043 false = true ∧ checkGlobalResetRow 2043 true = true := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 800000 in
set_option exponentiation.threshold 2048 in
theorem separate_reset_2044 :
    checkGlobalResetRow 2044 false = true ∧ checkGlobalResetRow 2044 true = true := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 800000 in
set_option exponentiation.threshold 2048 in
theorem separate_reset_2045 :
    checkGlobalResetRow 2045 false = true ∧ checkGlobalResetRow 2045 true = true := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 800000 in
set_option exponentiation.threshold 2048 in
theorem separate_reset_2046 :
    checkGlobalResetRow 2046 false = true ∧ checkGlobalResetRow 2046 true = true := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 800000 in
set_option exponentiation.threshold 2048 in
theorem separate_reset_2047 :
    checkGlobalResetRow 2047 false = true ∧ checkGlobalResetRow 2047 true = true := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 800000 in
set_option exponentiation.threshold 2048 in
theorem separate_reset_2048 :
    checkGlobalResetRow 2048 false = true ∧ checkGlobalResetRow 2048 true = true := by
  decide

theorem separate_high_block_pilot :
    [2033, 2034, 2035, 2036, 2037, 2038, 2039, 2040, 2041, 2042, 2043, 2044, 2045, 2046, 2047, 2048].all (fun a =>
      checkGlobalResetRow a false && checkGlobalResetRow a true) = true := by
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨separate_reset_2033, ⟨separate_reset_2034, ⟨separate_reset_2035, ⟨separate_reset_2036, ⟨separate_reset_2037, ⟨separate_reset_2038, ⟨separate_reset_2039, ⟨separate_reset_2040, ⟨separate_reset_2041, ⟨separate_reset_2042, ⟨separate_reset_2043, ⟨separate_reset_2044, ⟨separate_reset_2045, ⟨separate_reset_2046, ⟨separate_reset_2047, separate_reset_2048⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal


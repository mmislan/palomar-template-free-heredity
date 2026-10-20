import Lake
open Lake DSL

package palomarSubmissions where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "065356127b1dc0016f66b7283ce0ce2c4055aa55"

/- The source-only package retains the actual scientific module names.
   Building Solution recursively builds only its necessary frozen closure. -/
lean_lib ResearchProofs where
  roots := #[`proofs]
  globs := #[.submodules `proofs]
  leanOptions := #[⟨`warningAsError, true⟩]

lean_lib P161Formal where
  globs := #[.submodules `P161Formal]
  leanOptions := #[⟨`warningAsError, true⟩]

lean_lib Challenge where
  leanOptions := #[⟨`warningAsError, false⟩]

@[default_target]
lean_lib Solution where
  leanOptions := #[⟨`warningAsError, true⟩]

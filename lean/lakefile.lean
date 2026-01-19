import Lake
open Lake DSL

package «option-hedge-engine» where
  version := v!"0.1.0"
  keywords := #["formal verification", "options", "finance"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`pp.proofs.withType, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

@[default_target]
lean_lib OptionHedge where
  globs := #[.submodules `OptionHedge]
  -- Lean generates C files automatically in .lake/build/ir/
  -- These will be compiled to .o files by Lake

lean_exe verify_certs where
  root := `OptionHedge.Certificate.VerifierMain
  supportInterpreter := true

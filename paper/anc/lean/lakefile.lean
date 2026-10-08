import Lake
open Lake DSL

/-!
Lean spine of Part II (library `PositivityRigidityII`).

The only direct dependency is the Lean spine of Part I (library `PositivityRigidity`), which brings Mathlib
51e6992efd06126df61a496bebf8f49482a4e129 and Zeta23 fbdc36bbf17d20af3fd0447c6d1a8a02773c9844 with it
(`lake-manifest.json` pins every package at the revision of Part I's manifest; the toolchain is Part I's).
-/

package PositivityRigidityII where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`autoImplicit, false⟩]

-- Part I's spine: the public repository of Part I, tag v1.3 (commit 5bed664909d161fb148a0232e715f55f9a520f1b), Lean project in the
-- subdirectory paper/anc/lean.  The dependency is one line; lake-manifest.json pins the same commit.
require PositivityRigidity from git "https://github.com/nic410/zeta-positive-solutions" @ "5bed664909d161fb148a0232e715f55f9a520f1b" / "paper/anc/lean"

@[default_target]
lean_lib PositivityRigidityII

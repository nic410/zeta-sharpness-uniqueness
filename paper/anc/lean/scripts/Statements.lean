/-
Statement pin for the headline theorems and the axiom ledger (`scripts/audit.sh`, check (d)).

Roots: the headline theorems of Part II, every ledger axiom of Part II, and every ledger axiom of Part I on which a
headline theorem depends.  The script collects every declaration of the `PositivityRigidityII` *and*
`PositivityRigidity` modules that the statements of the roots unfold to: the types of the roots, and the transitive
closure through the types and bodies of definitions and the constructors of structures and inductives (theorems
other than the roots are not followed: a proof cannot change the meaning of a statement; Mathlib and Zeta23 are
pinned by `lake-manifest.json`).  Part I's definitions are included because the headline statements of Part II are
made of them (`κ*`, `𝒞`, `𝒦`, `p_ζ`, …): a change of Part I's spine that changes their meaning fails the audit.
For each declaration, sorted by name, it prints its kind, name, universe parameters, type and (for definitions)
body, pretty-printed with the options fixed below (docstrings are not printed), and a structural hash of the type
and body expressions, which also catches differences that the pretty-printer hides.

The expected output is `scripts/Statements.baseline.txt`; `scripts/audit.sh` requires an exact match.  A deliberate
change must regenerate the baseline:
  lake env lean scripts/Statements.lean > scripts/Statements.baseline.txt
-/
import PositivityRigidityII

open Lean Elab Command Meta

set_option pp.fullNames true
set_option pp.unicode.fun true
set_option format.width 110
set_option pp.numericTypes true
set_option pp.proofs false
set_option pp.funBinderTypes true
set_option pp.structureInstances true
set_option pp.fieldNotation false

namespace StatementsPinII

/-- The headline theorems whose statements are pinned. -/
def theoremRoots : List Name :=
  [``PosRigII.theorem1, ``PosRigII.theorem1_conductor, ``PosRigII.theorem1_finite,
   ``PosRigII.theorem1_object, ``PosRigII.theorem2, ``PosRigII.theorem2_condU, ``PosRigII.corollary3,
   ``PosRigII.corollary3_RH, ``PosRigII.corollary3_notRH, ``PosRigII.corollary_minimiser,
   ``PosRigII.main_summary, ``PosRigII.reduction, ``PosRigII.reduction_OPS,
   ``PosRigII.rh_iff_kappaOPS_zero, ``PosRigII.corollary8_2, ``PosRigII.corollary8_2_b,
   ``PosRigII.FT_window, ``PosRigII.kappaStar_nonneg_iff_kappaOPS_nonneg, ``PosRigII.transfer]

/-- The axioms declared in module `m`. -/
def axiomsOfModule (env : Environment) (m : Name) : List Name := Id.run do
  let mods := env.header.moduleNames
  let mut out : Array Name := #[]
  for i in [0:mods.size] do
    if mods[i]! == m then
      for n in env.header.moduleData[i]!.constNames do
        if let some (.axiomInfo _) := env.find? n then out := out.push n
  return (out.qsort (·.toString < ·.toString)).toList

/-- Is `n` declared in a module of Part II or Part I? -/
def isOurs (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i =>
    let m := env.header.moduleNames[i.toNat]!
    (`PositivityRigidityII).isPrefixOf m || (`PositivityRigidity).isPrefixOf m
  | none => false

/-- The declaration that carries the meaning of `n` (constructors and recursors → their inductive). -/
def owner (env : Environment) (n : Name) : Name :=
  match env.find? n with
  | some (.ctorInfo v) => v.induct
  | some (.recInfo v) => v.all.headD n
  | _ => n

/-- The constants a declaration's meaning depends on (theorems and axioms: their type only). -/
def deps (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | some (.defnInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.opaqueInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.axiomInfo v) => v.type.getUsedConstants
  | some (.thmInfo v) => v.type.getUsedConstants
  | some (.inductInfo v) => v.ctors.foldl (init := v.type.getUsedConstants) fun acc c =>
      match env.find? c with
      | some ci => acc ++ ci.type.getUsedConstants
      | none => acc
  | _ => #[]

def closure (env : Environment) (roots : List Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut worklist : Array Name := roots.toArray
  let mut out : Array Name := #[]
  while !worklist.isEmpty do
    let n := owner env worklist.back!
    worklist := worklist.pop
    if seen.contains n || !isOurs env n then continue
    seen := seen.insert n
    -- theorems are followed only if they are roots
    if let some (.thmInfo _) := env.find? n then
      unless roots.contains n do continue
    out := out.push n
    worklist := worklist ++ deps env n
  return out.qsort (·.toString < ·.toString)

def kindOf (env : Environment) : ConstantInfo → String
  | .inductInfo v => if isStructure env v.name then "structure" else "inductive"
  | .defnInfo _ => "def" | .opaqueInfo _ => "opaque" | .axiomInfo _ => "axiom"
  | .thmInfo _ => "theorem" | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor" | .quotInfo _ => "quot"

end StatementsPinII

open StatementsPinII in
run_cmd liftTermElabM do
  let env ← getEnv
  for r in theoremRoots do
    unless env.contains r do throwError "root {r} not found"
  let axII := axiomsOfModule env `PositivityRigidityII.Ledger
  let axIall := axiomsOfModule env `PositivityRigidity.Ledger
  let mut usedI : NameSet := {}
  for r in theoremRoots do
    for a in (← collectAxioms r) do
      if axIall.contains a then usedI := usedI.insert a
  let axI := (usedI.toList.toArray.qsort (·.toString < ·.toString)).toList
  let roots := theoremRoots ++ axII ++ axI
  let names := closure env roots
  IO.println s!"== statement pin: {names.size} declarations (closure of {theoremRoots.length} theorems, {axII.length} ledger axioms of Part II and {axI.length} ledger axioms of Part I) =="
  for n in names do
    let some ci := env.find? n | continue
    let us := if ci.levelParams.isEmpty then "" else s!".\{{", ".intercalate (ci.levelParams.map toString)}}"
    IO.println ""
    IO.println s!"{kindOf env ci} {n}{us}"
    IO.println s!"  : {← ppExpr ci.type}"
    let mut h : UInt64 := ci.type.hash
    match ci with
    | .defnInfo v =>
      IO.println s!"  := {← ppExpr v.value}"
      h := mixHash h v.value.hash
    | .opaqueInfo v =>
      IO.println s!"  := {← ppExpr v.value}"
      h := mixHash h v.value.hash
    | .inductInfo v =>
      for c in v.ctors do
        let some cc := env.find? c | continue
        IO.println s!"  | {c} : {← ppExpr cc.type}"
        h := mixHash h cc.type.hash
    | _ => pure ()
    IO.println s!"  hash {h}"

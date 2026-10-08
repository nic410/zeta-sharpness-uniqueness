/-
Axiom and dependency audit of the library `PositivityRigidityII` (run by `scripts/audit.sh`, which checks the
output).  Run (after `lake build`):  lake env lean scripts/Audit.lean

Prints a global scan of every declaration of the `PositivityRigidityII.*` modules:
1. the `axiom` declarations, by module: they must all be in `PositivityRigidityII.Ledger` (the ledger of Part II),
   and their number must equal the count in `LEDGER.md` (checked by `scripts/audit.sh`);
2. every axiom that some declaration depends on, other than `propext`, `Classical.choice`, `Quot.sound`, the ledger
   axioms of Part II and the ledger axioms of Part I (the axioms declared in `PositivityRigidity.Ledger`): must be
   none (this includes `sorryAx` and `Lean.ofReduceBool` / `Lean.trustCompiler`, the axioms behind `native_decide`);
3. the declarations that depend on `sorryAx` (must be none);
4. the ledger axioms of Part I on which some declaration of Part II depends (informational);
5. the headline theorems: each must exist and be a theorem.
-/
import PositivityRigidityII

open Lean Elab Command

namespace PosRigIIAudit

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The headline theorems: Theorems S and U, the Corollary, and Proposition `prop:reduction`. -/
def headlines : List Name :=
  [``PosRigII.theorem1, ``PosRigII.theorem1_conductor, ``PosRigII.theorem1_finite,
   ``PosRigII.theorem1_object, ``PosRigII.theorem2, ``PosRigII.theorem2_condU, ``PosRigII.corollary3,
   ``PosRigII.corollary3_RH, ``PosRigII.corollary3_notRH, ``PosRigII.corollary_minimiser,
   ``PosRigII.main_summary, ``PosRigII.reduction, ``PosRigII.reduction_OPS]

def showNames (l : List Name) : String :=
  if l.isEmpty then "none" else ", ".intercalate (l.map toString)

/-- The axioms declared in module `m`. -/
def axiomsOfModule (env : Environment) (m : Name) : Array Name := Id.run do
  let mods := env.header.moduleNames
  let mut out : Array Name := #[]
  for i in [0:mods.size] do
    if mods[i]! == m then
      for n in env.header.moduleData[i]!.constNames do
        if let some (.axiomInfo _) := env.find? n then out := out.push n
  return out.qsort (·.toString < ·.toString)

end PosRigIIAudit

open PosRigIIAudit in
run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let ledgerII := axiomsOfModule env `PositivityRigidityII.Ledger
  let ledgerI := axiomsOfModule env `PositivityRigidity.Ledger
  let mut nDecl := 0
  let mut outside : Array (Name × Name) := #[]
  let mut bad : Array (Name × Name) := #[]
  let mut sorryUsers : Array Name := #[]
  let mut usedI : NameSet := {}
  for i in [0:mods.size] do
    let m := mods[i]!
    unless (`PositivityRigidityII).isPrefixOf m do continue
    for n in env.header.moduleData[i]!.constNames do
      if n.isInternal then continue
      let some ci := env.find? n | continue
      nDecl := nDecl + 1
      if ci matches .axiomInfo _ then
        unless m == `PositivityRigidityII.Ledger do outside := outside.push (m, n)
      let axs ← collectAxioms n
      for a in axs do
        if ledgerI.contains a then usedI := usedI.insert a
        unless standardAxioms.contains a || ledgerII.contains a || ledgerI.contains a do
          bad := bad.push (n, a)
      if axs.contains ``sorryAx then sorryUsers := sorryUsers.push n
  IO.println "== global scan of the PositivityRigidityII.* modules =="
  IO.println s!"declarations scanned (non-internal): {nDecl}"
  IO.println s!"ledger axioms (axiom declarations in PositivityRigidityII.Ledger): {ledgerII.size}"
  for n in ledgerII do IO.println s!"  {n}"
  IO.println s!"axiom declarations outside PositivityRigidityII.Ledger: {if outside.isEmpty then "none" else toString outside}"
  IO.println s!"axioms other than propext / Classical.choice / Quot.sound and the ledger axioms of Parts I and II (incl. sorryAx, Lean.ofReduceBool = native_decide, Lean.trustCompiler): {if bad.isEmpty then "none" else toString bad}"
  IO.println s!"declarations depending on sorryAx: {if sorryUsers.isEmpty then "none" else toString sorryUsers}"
  let usedL := (usedI.toList.toArray.qsort (·.toString < ·.toString)).toList
  IO.println s!"Part I ledger axioms used by Part II ({usedL.length} of {ledgerI.size}): {showNames usedL}"
  IO.println "== headline theorems =="
  for n in headlines do
    match env.find? n with
    | some (.thmInfo _) =>
      let axs ← collectAxioms n
      let nonstd := (axs.toList.filter (fun a => !standardAxioms.contains a)).toArray.qsort (·.toString < ·.toString)
      IO.println s!"headline {n}: theorem; ledger axioms: {showNames nonstd.toList}"
    | some _ => IO.println s!"headline {n}: NOT A THEOREM"
    | none => IO.println s!"headline {n}: MISSING"

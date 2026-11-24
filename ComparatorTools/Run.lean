module

import all Lake.CLI.Check
import Lake.Config.InstallPath
import Lean.Elab.Import

open Lake Lean
open Lake.Check

private def readJson (path : System.FilePath) : IO Json := do
  IO.ofExcept (Json.parse (← IO.FS.readFile path))

private def selectConfig (repo : System.FilePath) (target : Option String) : IO Json := do
  let aggregate ← readJson (repo / "comparator.json")
  let some name := target | return aggregate
  let choices ← readJson (repo / "ComparatorChallenges" / "targets.json")
  let entry ← match choices.getObjVal? name with
    | .ok value => pure value
    | .error _ => throw (IO.userError s!"Unknown manuscript result: {name}. See the README index.")
  let challenge ← IO.ofExcept (entry.getObjValAs? String "challenge_module")
  let solution ← IO.ofExcept (entry.getObjValAs? String "solution_module")
  let statement ← IO.ofExcept (entry.getObjValAs? String "theorem")
  let support ← IO.ofExcept (entry.getObjValAs? (Array String) "support")
  return aggregate.setObjValAs! "challenge_module" challenge
    |>.setObjValAs! "solution_module" solution
    |>.setObjValAs! "theorem_names" (#[statement] ++ support)

private def checkImports (source : System.FilePath) : IO Unit := do
  let files ← source.walkDir
  for path in files do
    unless path.extension == some "lean" do continue
    unless (← path.symlinkMetadata).type == .file do
      throw (IO.userError s!"Expected an ordinary challenge source at {path}")
    let (imports, _, messages) ← Elab.parseImports (← IO.FS.readFile path) (some path.toString)
    if messages.hasErrors then throw (IO.userError s!"Invalid challenge imports in {path}")
    let localPath := path.toString.drop (source.toString.length + 1) |>.toString
    unless localPath.startsWith "Proof/" || localPath.startsWith "ComparatorChallenges/" do
      throw (IO.userError s!"Unexpected location for a frozen module: {path}")
    for imp in imports do
      if imp.module == `Init || (`Mathlib).isPrefixOf imp.module then continue
      unless (`ComparatorChallenges).isPrefixOf imp.module || (`Proof).isPrefixOf imp.module do
        throw (IO.userError s!"Unapproved import {imp.module} in {path}")
      let imported := (source / imp.module.toString.replace "." "/").addExtension "lean"
      let metadata ← try imported.symlinkMetadata catch _ =>
        throw (IO.userError s!"No frozen source for {imp.module} in {path}")
      unless metadata.type == .file do
        throw (IO.userError s!"Expected an ordinary frozen import at {imported}")

private def withExport (ctx : Context) (source : Name) (freshChallenge : Bool)
    (run : System.FilePath → IO UInt32) : IO UInt32 := do
  let (leanPath, binPath) ← safeResolveWorkspace.run ctx
  let targets := (← builtinTargets.run ctx) ++ ctx.theoremNames ++ ctx.legalAxioms ++
    (← primitiveTargets.run ctx) ++ ctx.definitionNames
  if freshChallenge then
    (runSandBoxed {
      cmd := ctx.whichLake.toString
      args := #["clean", "calderon_frozen_statements"]
      envPass := #["PATH"]
      readablePaths := #[ctx.projectDir, ctx.leanPrefix, ctx.lakeHome]
      writablePaths := #[ctx.projectDir / ".lake"]
      tmpfsPaths := forbiddenPaths }).run ctx
  safeLakeBuild #[source] |>.run ctx
  IO.println s!"Exporting {source}"
  IO.FS.withTempFile fun handle path => do
    (runSandBoxedWithStdoutTo handle {
      cmd := ctx.whichLean4Export.toString
      args := #[source.toString, "--"] ++ targets.map Name.toString
      envPass := #[]
      envOverride := #[("LEAN_ABORT_ON_PANIC", some "1"), ("LEAN_PATH", some leanPath),
        ("LEAN_SYSROOT", some ctx.leanPrefix.toString), ("PATH", some binPath)]
      readablePaths := #[ctx.projectDir, ctx.projectDir / ".lake", ctx.leanPrefix, ctx.whichLean4Export]
      writablePaths := #[]
      tmpfsPaths := forbiddenPaths }).run ctx
    run path

private def configure (lean : LeanInstall) (lake : LakeInstall) (workspace : System.FilePath)
    (config : Lake.Check.Config) : IO Context := do
  let .ok base ← mkContext "comparator" false false lean lake workspace {} |
    throw (IO.userError "Could not configure the stock Comparator sandbox")
  return { base with
    theoremNames := config.theorem_names.map String.toName
    definitionNames := config.definition_names.getD #[] |>.map String.toName
    legalAxioms := config.permitted_axioms.map String.toName }

public def main (args : List String) : IO UInt32 := do
  let repo ← IO.Process.getCurrentDir
  let frozen := repo / "ComparatorChallenges"
  let target ← match args with
    | [] => pure none
    | [name] => pure (some name)
    | _ => throw (IO.userError "Expected at most one manuscript result. See the README index.")
  checkImports (frozen / "Source")
  let configJson ← selectConfig repo target
  let config ← IO.ofExcept (fromJson? (α := Lake.Check.Config) configJson)
  let some lean ← findLeanInstall? | throw (IO.userError "Pinned Lean installation unavailable")
  let lake := LakeInstall.ofLean lean
  let challenge ← configure lean lake frozen config
  let solution ← configure lean lake repo config
  IO.FS.withTempFile fun handle path => do
    handle.putStr configJson.compress
    handle.flush
    withExport challenge config.challenge_module.toName true fun frozenExport =>
      withExport solution config.solution_module.toName false fun solutionExport => do
        let final ← IO.Process.spawn {
          cmd := lake.lake.toString
          args := #["comparator", "--config", path.toString,
            "--challenge-from-export", frozenExport.toString,
            "--solution-from-export", solutionExport.toString]
          cwd := some repo }
        final.wait

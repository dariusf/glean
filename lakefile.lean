import Lake

open Lake DSL
open System (FilePath)

package Glean

require subverso from git
  "https://github.com/leanprover/subverso" @ "52b9dfbd2658408e37ae6e8b72601ddeaaa25a0c"

lean_lib Glean where
  roots := #[`Glean.Main, `Glean.ExtractModule, `Glean.Render]

lean_exe «glean» where
  root := `Glean.Main

lean_exe «glean-extract-module» where
  root := `Glean.ExtractModule
  supportInterpreter := true

module_facet glean mod : FilePath := withRegisterJob s!"{mod.name}:glean" do
  let ws ← getWorkspace
  let exeJob ← «glean-extract-module».fetch
  let oleanJob ← mod.olean.fetch
  exeJob.bindM fun exeFile =>
    oleanJob.mapM fun oleanFile => do
      let outFile := mod.filePath (ws.root.buildDir / "glean" / "fragments") "json"
      addTrace (← fetchFileTrace exeFile)
      addTrace (← fetchFileTrace oleanFile)
      buildFileUnlessUpToDate' (text := true) outFile do
        proc {
          cmd := exeFile.toString
          args := #[mod.name.toString, outFile.toString]
          env := ← getAugmentedEnv
        }
      pure outFile

library_facet glean lib : FilePath := withRegisterJob s!"{lib.name}:glean" do
  let ws ← getWorkspace
  let mods ← (← lib.modules.fetch).await
  let jobs ← Job.mixArray <$> mods.mapM (·.facet `glean |>.fetch)
  jobs.mapM fun () => pure (ws.root.buildDir / "glean" / "fragments")

import Lean
import PfsProgs25.Unit13.ConstType

open Lean Json

unsafe
def main (args: List String) : IO Unit := do
  searchPathRef.set compile_time_search_path%
  enableInitializersExecution
  withImportModules #[Import.mk `Mathlib false, Import.mk `PfsProgs25.Unit13.ConstType false] {} 0 fun env => do
    let names ←  match args[0]? with
      | none => pure #[``Nat.succ_le_succ]
      | some f => do
        let lines ←  IO.FS.lines (System.mkFilePath [f])
        pure <| lines.map fun s => s.toName
    for name in names do
      let core :=
        getTypeCore name
      let eio? :=  core.run' {fileName := "", fileMap := {source:= "", positions := #[]}} {env := env}
      let io? ←  eio?.toIO'
      match io? with
      | Except.ok (some v) =>
        let js := Json.mkObj [("name", toJson name), ("type", v.pretty)]
        IO.println s!"{js.compress}"
      | Except.ok none => IO.println s!"none: type not found for {name}"
      | Except.error e => IO.println s!"{← e.toMessageData.toString}"

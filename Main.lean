import Atomization
import ImportGraph
import LeanExtras
open Lean Elab Command
-- TODO: a hack to get Repr for Lean.NameSet to print `#eval`s
deriving instance Repr for Lean.NameSet
deriving instance Repr for Std.HashMap
deriving instance Repr for ModuleIdx
-- deriving instance Repr for ConstMap
-- instance : Repr ConstMap where
--   reprPrec a _ _ := s!"{a.map₁} {a.map₂}"
-- deriving instance Repr for EnvironmentHeader
-- deriving instance Repr for EnvExtensionState
-- deriving instance Repr for Environment
-- /--To allow printing the environment for debugging-/
-- instance : ToString Environment where
--   toString := fun env => s!"{repr env}"

#eval (`Int).transitivelyUsedConstants


namespace InfoTreeUtils

def getInfoTreesForCurrentFile : IO (PersistentArray InfoTree) := do
  let path := System.FilePath.mk "Atomization/Basic.lean"
  let thisFile ← LeanFile.read path
  thisFile.getInfoTrees

deriving instance Repr for PersistentHashMap.Entry
deriving instance Repr for PersistentHashMap.Node
deriving instance Repr for PersistentHashMap
deriving instance Repr for ElabInfo
deriving instance Repr for FVarId
deriving instance Repr for LocalDecl
deriving instance Repr for PersistentArrayNode
deriving instance Repr for PersistentArray
deriving instance Repr for LocalContext
deriving instance Repr for TermInfo
deriving instance Repr for FileMap
deriving instance Repr for MVarId
deriving instance Repr for LocalInstance
deriving instance Repr for MetavarDecl
deriving instance Repr for DelayedMetavarAssignment
deriving instance Repr for MetavarContext
deriving instance Repr for Options
deriving instance Repr for OpenDecl
deriving instance Repr for NameGenerator
-- SMap Name ConstantInfo
deriving instance Repr for ConstantVal
deriving instance Repr for AxiomVal
deriving instance Repr for ReducibilityHints
deriving instance Repr for DefinitionVal
deriving instance Repr for TheoremVal
deriving instance Repr for OpaqueVal
deriving instance Repr for QuotKind
deriving instance Repr for QuotVal
deriving instance Repr for InductiveVal
deriving instance Repr for ConstructorVal
deriving instance Repr for RecursorRule
deriving instance Repr for RecursorVal
deriving instance Repr for ConstantInfo
deriving instance Repr for ConstMap
-- deriving instance Repr for EnvExtensionStateSpec
deriving instance Repr for CompletionInfo
deriving instance Repr for NameGenerator
deriving instance Repr for Environment
deriving instance Repr for CommandContextInfo
deriving instance Repr for ContextInfo
deriving instance Repr for CompletionInfo
-- #eval InfoTree.goalsAt?
#eval do
  let trees ← getInfoTreesForCurrentFile
  for tree in trees do
    let t := tree
    dbg_trace s!"{t.getCompletionInfos}"
    -- tree.termGoalAt? (String.Pos.mk 0)
  IO.println s!"We got {trees.size} top-level info trees from Main.lean"

end InfoTreeUtils




elab "#findCElab " c:command : command => do
  let env ← getEnv
  -- dbg_trace s!"{env}"
  let macroRes ← liftMacroM <| expandMacroImpl? env c
  match macroRes with
  | some (name, _) => logInfo s!"Next step is a macro: {name.toString}"
  | none =>
    let kind := c.raw.getKind
    let elabs := commandElabAttribute.getEntries (←getEnv) kind
    match elabs with
    | [] => logInfo s!"There is no elaborators for your syntax, looks like its bad :("
    | _ => logInfo s!"Your syntax may be elaborated by: {elabs.map (fun el => el.declName.toString)}"

#findCElab def lala := 12 -- Your syntax may be elaborated by: [Lean.Elab.Command.elabDeclaration]
#findCElab abbrev lolo := 12 -- Your syntax may be elaborated by: [Lean.Elab.Command.elabDeclaration]
#findCElab #check foo -- even our own syntax!: Your syntax may be elaborated by: [mySpecialCheck, Lean.Elab.Command.elabCheck]
#findCElab open Hi -- Your syntax may be elaborated by: [Lean.Elab.Command.elabOpen]
#findCElab namespace Foo -- Your syntax may be elaborated by: [Lean.Elab.Command.elabNamespace]
#findCElab #findCElab open Bar -- even itself!: Your syntax may be elaborated by: [«_aux_lean_elaboration___elabRules_command#findCElab__1»]

def f (x: Nat) : 2 * x ≥ x := by omega
#eval (`f).transitivelyUsedConstants

def main : IO Unit := do
  return ()
  -- let env := Lean.IR.getEnv
  --   env.displayStats
--   -- IO.println s!"Hello, {hello}!"

-- #eval Lean.Elab.InfoTree.hoverableInfoAt?
-- #eval do
--   let infoTrees <- Lean.Elab.getInfoTrees
--   for i in infoTrees do
--     i.

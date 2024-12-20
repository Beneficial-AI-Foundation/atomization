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

def f  := 2
#eval (`f).transitivelyUsedConstants

namespace InfoTreeUtils
#check Expr
-- `Lean.PrettyPrinter`
def getInfoTreesForFile (path : System.FilePath := "Atomization/Basic.lean") : IO (PersistentArray InfoTree) := do
  let thisFile ← LeanFile.read path
  thisFile.getInfoTrees


#print Int
-- deriving instance Repr for PersistentHashMap.Entry
-- deriving instance Repr for PersistentHashMap.Node
-- deriving instance Repr for PersistentHashMap
-- deriving instance Repr for ElabInfo
-- deriving instance Repr for FVarId
-- deriving instance Repr for LocalDecl
-- deriving instance Repr for PersistentArrayNode
-- deriving instance Repr for PersistentArray
-- deriving instance Repr for LocalContext
-- deriving instance Repr for TermInfo
-- deriving instance Repr for FileMap
-- deriving instance Repr for MVarId
-- deriving instance Repr for LocalInstance
-- deriving instance Repr for MetavarDecl
-- deriving instance Repr for DelayedMetavarAssignment
-- deriving instance Repr for MetavarContext
-- deriving instance Repr for Options
-- deriving instance Repr for OpenDecl
-- deriving instance Repr for NameGenerator
-- SMap Name ConstantInfo
-- deriving instance Repr for ConstantVal
-- deriving instance Repr for AxiomVal
-- deriving instance Repr for ReducibilityHints
-- deriving instance Repr for DefinitionVal
-- deriving instance Repr for TheoremVal
-- deriving instance Repr for OpaqueVal
-- deriving instance Repr for QuotKind
-- deriving instance Repr for QuotVal
-- deriving instance Repr for InductiveVal
-- deriving instance Repr for ConstructorVal
-- deriving instance Repr for RecursorRule
-- deriving instance Repr for RecursorVal
-- deriving instance Repr for ConstantInfo
-- deriving instance Repr for ConstMap
-- deriving instance Repr for EnvExtensionStateSpec
-- deriving instance Repr for CompletionInfo
-- deriving instance Repr for NameGenerator
-- deriving instance Repr for Environment
-- deriving instance Repr for CommandContextInfo
-- deriving instance Repr for ContextInfo
-- deriving instance Repr for CompletionInfo
-- #eval InfoTree.goalsAt?
-- #eval do
--   let trees ← getInfoTreesForCurrentFile
--   for tree in trees do
--     let t := tree
--     dbg_trace s!"{t.getCompletionInfos}"
--     -- tree.termGoalAt? (String.Pos.mk 0)
--   IO.println s!"We got {trees.size} top-level info trees from Main.lean"

end InfoTreeUtils


def matchOnTree (tree : InfoTree) : Syntax :=
  match tree with
  |.context _ tree => matchOnTree tree
  | .node (.ofTacticInfo info) children => info.stx
  | .node (.ofTermInfo info) children => info.stx
  -- | .node (.ofPartialTermInfo info)  => info.stx
  | .node (.ofCommandInfo info) children => info.stx
  | .node (.ofMacroExpansionInfo info) children => info.stx
  | .node (.ofOptionInfo info) children => info.stx
  | .node (.ofFieldInfo info) children => info.stx
  | .node (.ofCompletionInfo info) children => info.stx
  |.node (.ofUserWidgetInfo info) children => info.stx
  |.node (.ofCustomInfo info) children => info.stx
  -- |.node (.ofFVarAliasInfo info) children => Syntax.missing
  |.node (.ofFieldRedeclInfo info) children => info.stx
  |.node (.ofOmissionInfo info) children => info.stx
  -- |.node (.ofChoiceInfo info) children => info.stx
  | _ => Syntax.missing

elab "#atomize " path:str : command => do
  let trees ← InfoTreeUtils.getInfoTreesForFile (System.FilePath.mk ( path.getString))
  logInfo s!"{trees.size}"
  for tree in trees do
    let syn := matchOnTree tree
    let cmd <- liftCoreM (Lean.PrettyPrinter.formatCommand syn)
    logInfo s!"{cmd}"
      -- |.node info children => pure info
      -- | .node (.ofTacticInfo i) childern => pure i.stx
      -- | .node (.ofTermInfo i) children => pure i.stx
      -- | .node (.PartialTermInfo i) children => pure i.stx
      -- | .node (.ofCommandInfo i) children => pure i.stx
      -- | .node (.ofMacroExpansionInfo i) children => pure i.stx
      -- | .node (.ofOptionInfo i) children => pure i.stx
      -- | .node (.ofFieldInfo i) children => pure i.stx

      -- |.context => throwError "context"

-- `Lean.Syntax.Traverser`

#eval (`Int).transitivelyUsedConstants

elab "#atomize_name " name:ident : command => do
  let name := name.getId
  let trees ← name.getInfoTrees
  -- for tree in trees do
  --   let syn := matchOnTree tree
  --   let cmd <- liftCoreM (Lean.PrettyPrinter.formatCommand syn)
  --   logInfo s!"{cmd}"


-- #go "/Users/alokbeniwal/.elan/toolchains/leanprover--lean4---v4.12.0/src/lean/Lean/Expr.lean"
-- #atomize "/Users/alokbeniwal/.elan/toolchains/leanprover--lean4---v4.15.0-rc1/src/lean/Lean/Compiler/IR/Basic.lean"
-- Chris Bailey: Constant name -> pretty printer output

def main : IO Unit := do
  return ()

#eval (`Int).transitivelyUsedConstants
-- #eval (`Int).getUsedConstants

#printaxioms Int

-- this only works for module names, not declarations
#atomize_name Int
-- need: global const name -> the associated info tree

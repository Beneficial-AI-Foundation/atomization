import Atomization
import ImportGraph
import LeanExtras

open Lean Elab Command
-- TODO: a hack to get Repr for Lean.NameSet to print `#eval`s

-- To allow printing Lean.NameSet and Std.HashMap for `transitivelyUsedConstants`
deriving instance Repr for Lean.NameSet
deriving instance Repr for Std.HashMap

-- Make `Syntax` hashable for `matchOnTree` to put in `HashSet` later
deriving instance Hashable for Substring
deriving instance Hashable for SourceInfo
deriving instance Hashable for Syntax.Preresolved
deriving instance Hashable for Syntax




#eval (`Int).transitivelyUsedConstants



-- TODO: impl for single `Name`
def getInfoTreesForFile
  (path : System.FilePath := "Atomization/Basic.lean")
  : IO (PersistentArray InfoTree) := do
  (← LeanFile.read path).getInfoTrees


#print Int

/--Extracts the syntax from an info tree-/
def matchOnTree (tree : InfoTree) : Syntax :=
  match tree with
  | .context _ tree => matchOnTree tree
  | .node (.ofTacticInfo info) _
  | .node (.ofTermInfo info) _
  | .node (.ofCommandInfo info) _
  | .node (.ofMacroExpansionInfo info) _
  | .node (.ofOptionInfo info) _
  | .node (.ofFieldInfo info) _
  | .node (.ofCompletionInfo info) _
  | .node (.ofUserWidgetInfo info) _
  | .node (.ofCustomInfo info) _
  | .node (.ofFieldRedeclInfo info) _
  | .node (.ofOmissionInfo info) _ => info.stx
  -- `ofPartialTermInfo`, `ofFVarAliasInfo`, `ofChoiceInfo` are missing in Lean 4.12.0
  -- | .node (.ofPartialTermInfo info)  => info.stx
  -- |.node (.ofFVarAliasInfo info) children => Syntax.missing
  -- |.node (.ofChoiceInfo info) children => info.stx
  | _ => Syntax.missing

elab "#atomize " path:str : command => do
  let trees ← getInfoTreesForFile (System.FilePath.mk ( path.getString))
  logInfo s!"{trees.size}"
  for tree in trees do
    let syn := matchOnTree tree
    let cmd <- liftCoreM (Lean.PrettyPrinter.formatCommand syn)
    logInfo s!"{cmd}"


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
-- #atomize_name Int
-- need: global const name -> the associated info tree

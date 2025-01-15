import Atomization
-- import ImportGraph
-- -- import LeanExtras
-- import Lean.Elab
-- open Lean Elab Command
-- -- TODO: a hack to get Repr for Lean.NameSet to print `#eval`s

-- -- To allow printing Lean.NameSet and Std.HashMap for `transitivelyUsedConstants`
-- deriving instance Repr for Lean.NameSet
-- deriving instance Repr for Std.HashMap

-- deriving instance Hashable for Substring

-- deriving instance Hashable for SourceInfo
-- deriving instance Hashable for Syntax.Preresolved
-- deriving instance Hashable for Syntax
-- /-- Make `Syntax` hashable for `matchOnTree` to put in `HashSet` later-/
-- instance : Hashable Syntax where
--   hash := fun syn => Hashable.hash syn

-- #eval (`Int).transitivelyUsedConstants



-- TODO: impl for single `Name`
-- def getInfoTreesForFile
--   (path : System.FilePath := "Atomization/Basic.lean")
--   : IO (PersistentArray InfoTree) := do
--   (← LeanFile.read path).getInfoTrees


-- #print Int


-- #eval Lean.LocalDecl.toExpr

-- /--Extracts the syntax from an info tree-/
-- def matchOnTree (tree : InfoTree) : Syntax :=
--   match tree with
--   |.context _partialContext tree => matchOnTree tree
--   -- | .context partialContext tree => match partialContext with
--   --   | .commandCtx info => info.fileMap.source
--   --   | .parentDeclCtx name => do matchOnTree (← name.getInfoTrees)
--   | .node (.ofTacticInfo info) _
--   | .node (.ofTermInfo info) _
--   | .node (.ofCommandInfo info) _
--   | .node (.ofMacroExpansionInfo info) _
--   | .node (.ofOptionInfo info) _
--   | .node (.ofFieldInfo info) _
--   | .node (.ofCompletionInfo info) _
--   | .node (.ofUserWidgetInfo info) _
--   | .node (.ofCustomInfo info) _
--   | .node (.ofFieldRedeclInfo info) _
--   | .node (.ofOmissionInfo info) _ => info.stx
--   -- `ofPartialTermInfo`, `ofFVarAliasInfo`, `ofChoiceInfo` are missing in Lean 4.12.0
--   -- | .node (.ofPartialTermInfo info)  => info.stx
--   -- |.node (.ofFVarAliasInfo info) children => Syntax.missing
--   -- |.node (.ofChoiceInfo info) children => info.stx
--   | _ => Syntax.missing


-- -- idea: get all files that deps are defined in, then atomize those files
-- #eval Lean.Meta.inferType (Lean.Expr.lit (.natVal 1))
-- elab "#atomize " path:str : command => do
--   let maybeInfo := (<-getEnv).find? `f'
--   if h:maybeInfo.isSome then
--     let info := maybeInfo.get h
--     let name := info.value!
--     let type <- liftTermElabM (Lean.Meta.inferType name)
--     -- logInfo s!"{name}"
--     logInfo s!"{type}"
--     -- else
--       -- throwError "Int not found"

--   let path := System.FilePath.mk path.getString
--   let trees ← getInfoTreesForFile path
--   -- logInfo s!"{trees.size}"
--   for tree in trees do
--     let syn := matchOnTree tree
--     let cmd <- liftCoreM (Lean.PrettyPrinter.formatCommand syn)
--     logInfo s!"{cmd}"

-- #atomize "Atomization/Basic.lean"

-- `Lean.Syntax.Traverser`
-- deriving instance Lean.ToJson for Lean.Name

-- def _root_.Lean.Name.toJson  (name: Lean.Name) : Lean.Json := Lean.ToJson.toJson name

-- #eval (`fg).toJson
-- #eval (`Int).transitivelyUsedConstants

-- elab "#atomize_name " name:ident : command => do
--   let name := name.getId
--   let trees ← name.getInfoTrees
  -- for tree in trees do
  --   let syn := matchOnTree tree
  --   let cmd <- liftCoreM (Lean.PrettyPrinter.formatCommand syn)
  --   logInfo s!"{cmd}"


-- #go "/Users/alokbeniwal/.elan/toolchains/leanprover--lean4---v4.12.0/src/lean/Lean/Expr.lean"
-- #atomize "/Users/alokbeniwal/.elan/toolchains/leanprover--lean4---v4.15.0-rc1/src/lean/Lean/Compiler/IR/Basic.lean"
-- Chris Bailey: Constant name -> pretty printer output

def main : IO Unit := do
  -- let trees ← (`Int).getInfoTrees
  -- for tree in trees do
  --   let syn := matchOnTree tree
    -- let cmd <- liftCoreM (Lean.PrettyPrinter.formatCommand syn)
    -- logInfo s!"{cmd}"
  return ()

-- #eval (`Int).transitivelyUsedConstants
-- #eval (`Int).getUsedConstants

-- #printaxioms Int

-- this only works for module names, not declarations
-- #atomize_name Int
-- need: global const name -> the associated info tree

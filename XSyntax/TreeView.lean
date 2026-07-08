import Lean

namespace XSyntax

/-- A visible proof-state marker that carries the current tree-building event log.
    A frontend renderer can recognize this hypothesis and render it as SVG. -/
inductive TreeView : String → Prop where
  | intro (events : String) : TreeView events

def treeViewIntro (events : String) : TreeView events := TreeView.intro events

/-- Display-only notation for the live syntax-tree marker. -/
syntax:max (name := treeViewDisplay) "syntax_tree " str : term

open Lean PrettyPrinter.Delaborator SubExpr in
@[delab app.XSyntax.TreeView]
def delabTreeView : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 1)
  let str ← match e.getArg! 0 with
    | .lit (.strVal v) => pure v
    | _ => failure
  let strStx := Syntax.mkStrLit str
  `(syntax_tree $strStx)

end XSyntax

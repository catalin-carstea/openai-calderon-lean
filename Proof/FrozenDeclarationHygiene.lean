import Lean

open Lean Elab Command

/-- Disposable source-level quotation-context compatibility wrapper.
The underlying source declaration is passed to the ordinary elaborator.
Only the quotation-context module prefix changes; Env.mainModule never does. -/
elab "compat_solution_hygiene " c:command : command => do
  unless c.raw.isOfKind ``Lean.Parser.Command.declaration do
    throwError "ordinary declaration expected"
  let modifiers ← elabModifiers ⟨c.raw[0]⟩
  let view ← mkDefView modifiers c.raw[1]
  let views := #[view]
  let sc ← getScope
  withInitQuotContext (some (hash (views.map (·.declId[0].getId)))) do
    let ctx ← MonadQuotation.getContext
    let historical := ctx.replacePrefix (← getEnv).mainModule `Solution
    withReader (fun ctx => { ctx with quotContext? := some historical }) do
      runTermElabM fun vars => Term.elabMutualDef vars sc views


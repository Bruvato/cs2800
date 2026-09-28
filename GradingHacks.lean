import Lean.Elab.ElabRules
import Lean.Elab.Frontend

namespace RawSource

open Lean

private structure Frame where
  path : Name
  bodyStart : String.Pos.Raw
  isSection : Bool

/--
`endopen Question1` closes the namespace `Question1` and immediately opens it,
so the declarations inside remain visible afterwards. It is equivalent to
`end Question1` followed by `open Question1`, and `raw`, `elab_sec`, and
`empty_sec` treat it as an ordinary `end` when scanning the source.
-/
syntax (name := endOpen) "endopen " ident : command

open Lean.Elab.Command in
elab_rules : command
  | `(endopen $namespaceName:ident) => do
    elabCommand (← `(end $namespaceName))
    elabCommand (← `(open $namespaceName:ident))

/--
`hide Solutions` is `namespace Solutions` under a name that marks the block as
instructor-only, so tooling can strip it from a distributed file. Close it with
`end` or `endopen`, exactly like a namespace.
-/
macro (name := hide) "hide " namespaceName:ident : command =>
  `(namespace $namespaceName)

/-- `nshide` is `hide` under its explicitly namespace-flavored name. -/
macro (name := nsHide) "nshide " namespaceName:ident : command =>
  `(namespace $namespaceName)

/-- `sechide` is the `section` counterpart of `nshide`. -/
macro (name := secHide) "sechide " sectionName:(ident)? : command =>
  match sectionName with
  | some name => `(section $name)
  | none => `(section)

/-- Scope option holding the namespace that the matching `end` should open. -/
private def pendingOpen : Name := `RawSource.question

/--
`question Question1` is `namespace Question1` whose matching `end Question1`
also opens the namespace, so a plain `end` behaves like `endopen`. The request
lives in the scope that `namespace` pushes, so a nested `section` or
`namespace` closed by its own `end` is unaffected.
-/
syntax (name := question) "question " ident : command

open Lean.Elab.Command in
elab_rules : command
  | `(question $namespaceName:ident) => do
    elabCommand (← `(namespace $namespaceName))
    modifyScope fun scope =>
      { scope with opts := scope.opts.set pendingOpen namespaceName.getId }

/--
This shadows the builtin `end` so that it can open a namespace entered with
`question`. The parser mirrors the builtin one, so delegating is a matter of
replacing the syntax kind; everything else is left to the builtin elaborator.
-/
syntax (name := endQuestion) (priority := high) "end"
  (ppSpace colGt Lean.Parser.identWithPartialTrailingDot)? : command

open Lean.Elab.Command in
@[command_elab endQuestion] def elabEndQuestion : CommandElab := fun stx => do
  let pending : Name := (← getScope).opts.get pendingOpen Name.anonymous
  elabCommand (stx.setKind ``Parser.Command.end)
  if stx[1].getNumArgs > 0 then
    let closed : Ident := ⟨stx[1][0]⟩
    if !pending.isAnonymous && pending == closed.getId then
      elabCommand (← `(open $closed:ident))

/-- Read a section body using parsed command boundaries, not text matching. -/
private partial def findBody (input : Parser.InputContext)
    (context : Parser.ParserModuleContext) (target : Name)
    (state : Parser.ModuleParserState) (stack : List Frame := []) :
    Except String String := do
  let (command, next, messages) := Parser.parseCommand input context state {}
  if messages.hasErrors then
    let position := input.fileMap.toPosition state.pos
    throw s!"raw: cannot parse source near line {position.line}"
  if Parser.isTerminalCommand command then
    throw s!"raw: section '{target}' was not found or is not closed"
  let kind := command.getKind
  let opensNamespace := kind == ``Parser.Command.namespace || kind == ``«hide»
    || kind == ``nsHide || kind == ``«question»
  let opensSection := kind == ``Parser.Command.section || kind == ``secHide
  if opensNamespace || opensSection then
    let parent := (stack.head?).map (·.path) |>.getD Name.anonymous
    -- Namespace commands have a required identifier rather than an optional one.
    let label := if opensNamespace then command.getArgs.back!.getId else
      command.getArgs.back!.getOptional?.map Syntax.getId |>.getD Name.anonymous
    let frame : Frame := {
      path := parent ++ label
      bodyStart := command.getTailPos?.getD next.pos
      isSection := opensSection && !label.isAnonymous }
    findBody input context target next (frame :: stack)
  else if kind == ``Parser.Command.end || kind == ``endOpen
      || kind == ``endQuestion then
    match stack with
    | frame :: rest =>
      if frame.isSection && frame.path == target then
        return (input.substring frame.bodyStart
          (command.getPos?.getD state.pos)).toString
      findBody input context target next rest
    | [] => throw "raw: unmatched 'end' in source"
  else
    findBody input context target next stack

/--
`raw Question1.Spec` is a String containing the exact source between the
opening `section Spec` command and its matching `end` or `endopen` in the
current file.
Comments, whitespace, and nested sections are preserved; the two delimiting
commands are excluded. Named enclosing sections/namespaces form the dotted
path. The first matching closed section is used.

This is term syntax, not a runtime function: section names are not Lean values.
It uses the editor's source buffer and the parser available at the call site,
so place calls after the section and any syntax declarations it uses.
-/
syntax (name := raw) "raw " ident : term

private def sectionBody (sectionName : Syntax) : Elab.Term.TermElabM String := do
  let fileMap ← getFileMap
  let input := Parser.mkInputContext fileMap.source (← getFileName)
  let (_, state, messages) ← Parser.parseHeader input
  if messages.hasErrors then
    throwError "raw: cannot parse the source file header"
  let context : Parser.ParserModuleContext := {
    env := ← getEnv
    options := ← getOptions
    currNamespace := ← getCurrNamespace
    openDecls := ← getOpenDecls }
  match findBody input context sectionName.getId state with
  | .ok body => return body
  | .error message => throwErrorAt sectionName "{message}"

open Lean.Elab Lean.Elab.Term in
elab_rules : term
  | `(raw $sectionName:ident) => do
    return mkStrLit (← sectionBody sectionName)

/--
`elab_sec Question1.Spec` checks the extracted commands in a separate copy of
the call-site environment and returns `true` exactly when they have no errors.
Warnings (including `sorry`) do not count as errors. Checking happens during
term elaboration; the resulting term is a Bool literal.

Earlier declarations, the current namespace, open declarations, and options
are available. Term-local variables and section `variable` binders are not
copied. Declarations and option changes made while checking are discarded,
but IO performed by commands such as `#eval` is not sandboxed. Re-declaring an
existing named declaration is an error, just as in ordinary Lean.
-/
syntax (name := elabSec) "elab_sec " ident : term

open Lean.Elab Lean.Elab.Term in
elab_rules : term
  | `(elab_sec $sectionName:ident) => do
    let body ← sectionBody sectionName
    let options := (← getOptions).setBool `Elab.async false
    let initial := Command.mkState (← getEnv) {} options
    let scope := { initial.scopes.head! with
      currNamespace := ← getCurrNamespace
      openDecls := ← getOpenDecls }
    let input := Parser.mkInputContext body
      s!"{← getFileName} (elab_sec {sectionName.getId})"
    let checked ← IO.processCommands input {} { initial with scopes := [scope] }
    return mkConst (if checked.commandState.messages.hasErrors then
      ``Bool.false else ``Bool.true)

/-- Recognize only whitespace and comments, including nested/doc comments. -/
private def onlyComments : List Char → Nat → Bool → Bool
  | [], depth, _ => depth == 0
  | '\n' :: rest, 0, true => onlyComments rest 0 false
  | _ :: rest, 0, true => onlyComments rest 0 true
  | '/' :: '-' :: rest, depth, false => onlyComments rest (depth + 1) false
  | '-' :: '/' :: rest, depth + 1, false => onlyComments rest depth false
  | '-' :: '-' :: rest, 0, false => onlyComments rest 0 true
  | c :: rest, 0, false => c.isWhitespace && onlyComments rest 0 false
  | _ :: rest, depth + 1, inLine => onlyComments rest (depth + 1) inLine

/--
`empty_sec Question1.Spec` returns a Bool indicating whether the section body
contains only whitespace and comments. Nested block comments and documentation
comments count as comments; nested section commands count as content.
-/
syntax (name := emptySec) "empty_sec " ident : term

open Lean.Elab Lean.Elab.Term in
elab_rules : term
  | `(empty_sec $sectionName:ident) => do
    let body ← sectionBody sectionName
    return mkConst (if onlyComments body.toList 0 false then
      ``Bool.true else ``Bool.false)

end RawSource

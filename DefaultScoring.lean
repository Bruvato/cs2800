import GradingHacks

def mk_message (labels : List (Bool × String)) : String :=
  String.intercalate "\n" <|
    labels.map fun (bit, label) =>
      s!"{label}: {if bit then "yes" else "no"}"

-- Define the standard bits from a question's Answer and Spec sections.
macro "def_bits " q:ident : command => do
  let ns := Lean.mkIdent `Bits
  let empty := Lean.mkIdent `empty
  let passes := Lean.mkIdent `passes
  let answer := Lean.mkIdent (q.getId ++ `Answer)
  let spec := Lean.mkIdent (q.getId ++ `Spec)
  `(namespace $ns
      def $empty := (empty_sec $answer)
      def $passes := (elab_sec $spec)
    end $ns)

-- Define the standard one-point score from a question's bits.
macro "def_score " q:ident : command => do
  let ns := Lean.mkIdent `Score
  let maxScore := Lean.mkIdent `maxScore
  let score := Lean.mkIdent `score
  let empty := Lean.mkIdent (q.getId ++ `Bits.empty)
  let passes := Lean.mkIdent (q.getId ++ `Bits.passes)
  `(namespace $ns
      def $maxScore : Nat := 1
      def $score : Nat :=
        if $empty then 0 else if $passes then $maxScore else 0
      #eval $score
    end $ns)

-- Build the standard labels from a question's Bits namespace.
macro "def_labels " q:ident : term => do
  let empty := Lean.mkIdent (q.getId ++ `Bits.empty)
  let passes := Lean.mkIdent (q.getId ++ `Bits.passes)
  `(([ (!$empty, "Answer submitted")
     , ($passes, "Passes Spec")
     ] : List (Bool × String)))

-- Define the Message namespace and its standard message.
macro "def_message " q:ident : command => do
  let ns := Lean.mkIdent `Message
  let name := Lean.mkIdent `message
  `(namespace $ns
      def $name : String := mk_message (def_labels $q)
    end $ns)

-- Define all standard grading namespaces for the enclosing question.
elab "gradescope_defaults" : command => do
  let ns ← Lean.getCurrNamespace
  if ns.isAnonymous then
    throwError "gradescope_defaults must be used inside a question namespace"
  let q := Lean.mkIdent ns
  Lean.Elab.Command.elabCommand (←
    `(def_bits $q
      def_message $q
      def_score $q))

-- Treat the hidden marker as a no-op around any Lean command.
macro "hidden" cmd:command : command => pure cmd

/-
  Reading C: tokens of a line, and the `#define`s of a header, into the semantics' terms.
-/
import Semantics

namespace PP

def tokenize (s : String) : List String :=
  let rec go (cs : List Char) (cur : String) (acc : List String) : List String :=
    let flush := if cur.isEmpty then acc else cur :: acc
    match cs with
    | [] => flush.reverse
    | '#' :: '#' :: r => go r "" ("##" :: flush)
    | '.' :: '.' :: '.' :: r => go r "" ("..." :: flush)
    | c :: r =>
      if identChar c then go r (cur.push c) acc
      else if c.isWhitespace then go r "" flush
      else go r "" (c.toString :: flush)
  go s.toList "" []

def dropWs (cs : List Char) : List Char := cs.dropWhile Char.isWhitespace
def trimChars (cs : List Char) : List Char := (dropWs (dropWs cs).reverse).reverse

def splitChars (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: r =>
    let rest := splitChars sep r
    if c == sep then [] :: rest else (c :: rest.headD []) :: rest.tail

/-- One `#define`, its text after the directive: the name, then `(` at once for a
    function-like macro. -/
def parseDefine (text : List Char) : Option (Name × Def) := do
  let cs := dropWs text
  let nameCs := cs.takeWhile identChar
  guard (!nameCs.isEmpty)
  let name := String.ofList nameCs
  let rest := cs.drop nameCs.length
  match rest with
  | '(' :: r =>
    let inside := r.takeWhile (· != ')')
    let bodyText := String.ofList ((r.dropWhile (· != ')')).drop 1)
    let ps := (splitChars ',' inside).map (fun p => String.ofList (trimChars p)) |>.filter (· != "")
    let variadic := ps.getLast? == some "..."
    let named := if variadic then ps.dropLast else ps
    let body := (tokenize bodyText).map fun t =>
      if t == "##" then BTok.paste
      else if t == "__VA_ARGS__" && variadic then BTok.va
      else match named.idxOf? t with
        | some i => BTok.param i
        | none => BTok.tok t
    return (name, .fn named.length variadic body)
  | _ =>
    let body := (tokenize (String.ofList rest)).map fun t => if t == "##" then BTok.paste else BTok.tok t
    return (name, .obj body)

/-- The lines of a header with `\`-newlines joined and `//` comments dropped. -/
def logicalLines (src : String) : List (List Char) :=
  let rec join : List Char → List Char
    | [] => []
    | '\\' :: '\n' :: r => join r
    | c :: r => c :: join r
  let rec cut : List Char → List Char
    | [] => []
    | '/' :: '/' :: _ => []
    | c :: r => c :: cut r
  (splitChars '\n' (join src.toList)).map cut

/-- Its `#define`s, later ones first (a redefinition wins). -/
def defines (src : String) : Env :=
  (logicalLines src).filterMap (fun l =>
    let t := dropWs l
    if t.take 7 == "#define".toList then parseDefine (t.drop 7) else none) |>.reverse

def input (s : String) : List Tok := (tokenize s).map fun t => { s := t }

def run (Γ : Env) (fuel : Nat) (s : String) : Option (List String) :=
  (expand Γ fuel 1 (input s)).map fun (out, _, _) => out.map (·.s)

/-- The steps of a run, as §2 numbers them (1, 2, ...; 0 is the input's origin). -/
def steps (Γ : Env) (fuel : Nat) (s : String) : Option (List Step) :=
  (expand Γ fuel 1 (input s)).map fun (_, st, _) => st

def groups (out : List String) : Nat := out.count "~"

end PP

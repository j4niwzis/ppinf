/-
  pp_primrec.tex §1, the reduction rules, as an executable Lean definition.

  A token is a spelling with its hidden names. The environment Γ maps a name to an object
  body or to parameters and a body. `scan` is S, `expand` is E = F ∘ S; arguments are
  expanded on their own, before rescanning (E(A_i)), except next to `##`; `paste` reduces
  the original `##` operators left to right, then erases placemarkers; `mark K` is M_K.
  Rewriting is bounded by a fuel argument: `none` when it runs out or a rule cannot apply
  (unbalanced parentheses, wrong arity, an invalid paste).
-/

namespace PP

abbrev Name := String

/-- A token: its spelling, its hidden names, and -- for §2 -- its origin: the step that made
    it (`o`, 0 for input) and that step's mark (`P`). -/
structure Tok where
  s : String
  H : List Name := []
  o : Nat := 0
  P : List Name := []
  deriving Repr, DecidableEq, Inhabited

/-- A rewrite step, as §2 sees it: the macro, its head and closing parenthesis (none for an
    object macro), its mark, and its number. -/
structure Step where
  m : Name
  head : Tok
  close : Option Tok
  mark : List Name
  id : Nat
  deriving Repr, Inhabited

/-- A body element: a token, a parameter (its index; the variadic one is `va`), or `##`. -/
inductive BTok where
  | tok (s : String)
  | param (i : Nat)
  | va
  | paste
  deriving Repr, DecidableEq, Inhabited

inductive Def where
  | obj (body : List BTok)
  | fn (arity : Nat) (variadic : Bool) (body : List BTok)
  deriving Repr, Inhabited

abbrev Env := List (Name × Def)

def Env.find (Γ : Env) (m : Name) : Option Def := (Γ.find? (·.1 == m)).map (·.2)

/-! Pasting. Two pp-tokens paste to one where their spellings together are one: here,
    identifiers and numbers (letters, digits, `_`), and `#` `#`. -/

def identChar (c : Char) : Bool := c.isAlphanum || c == '_'

def pasted (a b : String) : Option String :=
  let ab := a ++ b
  if ab.all identChar && !ab.isEmpty then some ab
  else if a == "#" && b == "#" then some "##"
  else none

/-- A replacement element: a token, a placemarker, or an original `##` operator. -/
inductive RTok where
  | t (x : Tok)
  | pm
  | op
  deriving Repr, Inhabited

def inter (H J : List Name) : List Name := H.filter (· ∈ J)
def union (K H : List Name) : List Name := K ++ H.filter (· ∉ K)

def pasteTwo : RTok → RTok → Option RTok
  | .pm, x => some x
  | x, .pm => some x
  | .t a, .t b => (pasted a.s b.s).map fun s => .t { s, H := inter a.H b.H }
  | _, _ => none

/-- P: the `##` operators, left to right, then the placemarkers erased. -/
def paste (xs : List RTok) : Option (List Tok) :=
  let rec go : List RTok → List RTok → Option (List RTok)
    | acc, [] => some acc.reverse
    | a :: acc, .op :: b :: rest => do let c ← pasteTwo a b; go (c :: acc) rest
    | _, .op :: _ => none
    | acc, x :: rest => go (x :: acc) rest
  (go [] xs).map fun ys => ys.filterMap fun | .t x => some x | _ => none

/-- M_K, by step `e`: every token of its replacement gets `K` and the origin `e`. -/
def mark (e : Nat) (K : List Name) (xs : List Tok) : List Tok :=
  xs.map fun x => { x with H := union K x.H, o := e, P := K }

/-- F: a token keeps only its own spelling as hidden, where it was hidden. -/
def finalize (xs : List Tok) : List Tok := xs.map fun x => { x with H := if x.s ∈ x.H then [x.s] else [] }

/-! Arguments: the tokens up to the matching closing parenthesis, returned with it (its
    hidden set is J); split at commas outside nested parentheses; the variadic slot is the
    suffix after the named ones, its own commas kept. -/

def closeAt : Nat → List Tok → List Tok → Option (List Tok × Tok × List Tok)
  | _, [], _ => none
  | d, x :: rest, acc =>
    if x.s == ")" then (if d == 0 then some (acc.reverse, x, rest) else closeAt (d - 1) rest (x :: acc))
    else if x.s == "(" then closeAt (d + 1) rest (x :: acc)
    else closeAt d rest (x :: acc)

def depthAfter (d : Nat) (x : Tok) : Nat := if x.s == "(" then d + 1 else if x.s == ")" then d - 1 else d

def splitTop : Nat → List Tok → List Tok → List (List Tok)
  | _, [], cur => [cur.reverse]
  | d, x :: rest, cur =>
    if x.s == "," && d == 0 then cur.reverse :: splitTop d rest []
    else splitTop (depthAfter d x) rest (x :: cur)

/-- What follows the `k`-th comma outside parentheses. -/
def afterCommas : Nat → Nat → List Tok → List Tok
  | 0, _, xs => xs
  | _ + 1, _, [] => []
  | k + 1, d, x :: rest =>
    if x.s == "," && d == 0 then afterCommas k d rest else afterCommas (k + 1) (depthAfter d x) rest

/-- The arguments bound to the parameters: the named ones, and the variadic suffix. -/
def bind (arity : Nat) (variadic : Bool) (inner : List Tok) : Option (List (List Tok) × List Tok) :=
  let as := splitTop 0 inner []
  if variadic then
    if as.length < arity then
      (if as.length + 1 == arity || (arity == 0) then some (as ++ List.replicate (arity - as.length) [], []) else none)
    else some (as.take arity, afterCommas arity 0 inner)
  else if arity == 0 then (if as == [[]] then some ([], []) else none)
  else if as.length == arity then some (as, []) else none

def adjacentPaste (body : List BTok) (i : Nat) : Bool :=
  (i > 0 && body[i - 1]? == some .paste) || body[i + 1]? == some .paste

/-- A token passed by, put before what the scan of the rest gives. -/
def emit (x : Tok) (r : Option (List Tok × List Step × Nat)) : Option (List Tok × List Step × Nat) :=
  r.map fun q => (x :: q.1, q.2.1, q.2.2)

/-- A step's replacement scanned again with the rest: the steps of its arguments first, then
    the step, then the rescan's. -/
def after (step : Step) (st₁ : List Step) (r : Option (List Tok × List Step × Nat)) :
    Option (List Tok × List Step × Nat) :=
  r.map fun q => (q.1, st₁ ++ step :: q.2.1, q.2.2)

mutual
/-- S, with `fuel` rewrite steps at most, steps numbered from `c`: the output, the steps
    taken (in order), and the next number. -/
def scan (Γ : Env) : Nat → Nat → List Tok → Option (List Tok × List Step × Nat)
  | 0, _, _ => none
  | _ + 1, c, [] => some ([], [], c)
  | n + 1, c, x :: rest =>
    if x.s ∈ x.H then emit x (scan Γ n c rest) else
    match Γ.find x.s with
    | some (.obj body) =>
      (subst Γ n (c + 1) body [] []).bind fun r =>
      (paste r.1).bind fun b =>
      after { m := x.s, head := x, close := none, mark := x.s :: x.H, id := c } r.2.1
        (scan Γ n r.2.2 (mark c (x.s :: x.H) b ++ rest))
    | some (.fn arity variadic body) =>
      match rest with
      | open_ :: after' =>
        if open_.s != "(" then emit x (scan Γ n c rest) else
        (closeAt 0 after' []).bind fun a =>
        (bind arity variadic a.1).bind fun bd =>
        (subst Γ n (c + 1) body bd.1 bd.2).bind fun r =>
        (paste r.1).bind fun b =>
        after { m := x.s, head := x, close := some a.2.1, mark := x.s :: inter x.H a.2.1.H, id := c } r.2.1
          (scan Γ n r.2.2 (mark c (x.s :: inter x.H a.2.1.H) b ++ a.2.2))
      | [] => some ([x], [], c)
    | none => emit x (scan Γ n c rest)

/-- E = F ∘ S. -/
def expand (Γ : Env) (n c : Nat) (xs : List Tok) : Option (List Tok × List Step × Nat) :=
  (scan Γ n c xs).map fun q => (finalize q.1, q.2.1, q.2.2)

/-- sub_A(B): parameters next to `##` as they are (a placemarker where empty), others
    expanded on their own; other body tokens fresh. -/
def subst (Γ : Env) (n c : Nat) (body : List BTok) (named : List (List Tok)) (vaArg : List Tok) :
    Option (List RTok × List Step × Nat) :=
  substFrom Γ n body body 0 c named vaArg

def substFrom (Γ : Env) (n : Nat) (whole : List BTok) :
    List BTok → Nat → Nat → List (List Tok) → List Tok → Option (List RTok × List Step × Nat)
  | [], _, c, _, _ => some ([], [], c)
  | b :: bs, i, c, named, vaArg =>
    (piece Γ n whole b i c named vaArg).bind fun p =>
    (substFrom Γ n whole bs (i + 1) p.2.2 named vaArg).map fun q => (p.1 ++ q.1, p.2.1 ++ q.2.1, q.2.2)

/-- One body element substituted. -/
def piece (Γ : Env) (n : Nat) (whole : List BTok) (b : BTok) (i c : Nat) (named : List (List Tok))
    (vaArg : List Tok) : Option (List RTok × List Step × Nat) :=
  match b with
  | .tok s => some ([RTok.t { s }], [], c)
  | .paste => some ([RTok.op], [], c)
  | .param j => one Γ n whole (named.getD j []) i c
  | .va => one Γ n whole vaArg i c

/-- A parameter: as it is next to `##` (a placemarker where empty), else expanded alone. -/
def one (Γ : Env) (n : Nat) (whole : List BTok) (a : List Tok) (i c : Nat) : Option (List RTok × List Step × Nat) :=
  if adjacentPaste whole i then some (if a.isEmpty then [RTok.pm] else a.map RTok.t, [], c)
  else (expand Γ n c a).map fun q => (q.1.map RTok.t, q.2.1, q.2.2)
end

end PP

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

structure Tok where
  s : String
  H : List Name := []
  deriving Repr, DecidableEq, Inhabited

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

def mark (K : List Name) (xs : List Tok) : List Tok := xs.map fun x => { x with H := union K x.H }

/-- F: a token keeps only its own spelling as hidden, where it was hidden. -/
def finalize (xs : List Tok) : List Tok := xs.map fun x => { x with H := if x.s ∈ x.H then [x.s] else [] }

/-! Arguments: split at commas outside nested parentheses; the closing parenthesis
    returned with its hidden set (J). -/

def args : Nat → List Tok → List Tok → List (List Tok) → List Tok → Option (List (List Tok) × Tok × List Tok)
  | _, [], _, _, _ => none
  | d, x :: rest, cur, done, _ =>
    if x.s == ")" then
      if d == 0 then some ((done ++ [cur.reverse]), x, rest)
      else args (d - 1) rest (x :: cur) done []
    else if x.s == "(" then args (d + 1) rest (x :: cur) done []
    else if x.s == "," && d == 0 then args d rest [] (done ++ [cur.reverse]) []
    else args d rest (x :: cur) done []

/-- The arguments bound to the parameters: the named ones, and the variadic suffix joined by
    its commas. -/
def bind (arity : Nat) (variadic : Bool) (as : List (List Tok)) : Option (List (List Tok) × List Tok) :=
  if variadic then
    if as.length < arity then
      (if as.length + 1 == arity || (arity == 0) then some (as ++ List.replicate (arity - as.length) [], []) else none)
    else some (as.take arity, List.intercalate [{ s := "," }] (as.drop arity))
  else if arity == 0 then (if as == [[]] then some ([], []) else none)
  else if as.length == arity then some (as, []) else none

def adjacentPaste (body : List BTok) (i : Nat) : Bool :=
  (i > 0 && body[i - 1]? == some .paste) || body[i + 1]? == some .paste

mutual
/-- S, with `fuel` rewrite steps at most. -/
def scan (Γ : Env) : Nat → List Tok → Option (List Tok)
  | 0, _ => none
  | _ + 1, [] => some []
  | n + 1, x :: rest =>
    if x.s ∈ x.H then (scan Γ n rest).map (x :: ·) else
    match Γ.find x.s with
    | some (.obj body) => do
      let r ← subst Γ n body [] []
      let b ← paste r
      scan Γ n (mark (x.s :: x.H) b ++ rest)
    | some (.fn arity variadic body) =>
      match rest with
      | open_ :: after =>
        if open_.s != "(" then (scan Γ n rest).map (x :: ·) else do
        let (as, close, after') ← args 0 after [] [] []
        let (named, vaArg) ← bind arity variadic as
        let r ← subst Γ n body named vaArg
        let b ← paste r
        scan Γ n (mark (x.s :: inter x.H close.H) b ++ after')
      | [] => some [x]
    | none => (scan Γ n rest).map (x :: ·)

/-- E = F ∘ S. -/
def expand (Γ : Env) (n : Nat) (xs : List Tok) : Option (List Tok) := (scan Γ n xs).map finalize

/-- sub_A(B): parameters next to `##` as they are (a placemarker where empty), others
    expanded on their own; other body tokens fresh. -/
def subst (Γ : Env) (n : Nat) (body : List BTok) (named : List (List Tok)) (vaArg : List Tok) :
    Option (List RTok) :=
  substFrom Γ n body body 0 named vaArg

def substFrom (Γ : Env) (n : Nat) (whole : List BTok) : List BTok → Nat → List (List Tok) → List Tok → Option (List RTok)
  | [], _, _, _ => some []
  | b :: bs, i, named, vaArg => do
    let here ← match b with
      | .tok s => some [RTok.t { s }]
      | .paste => some [RTok.op]
      | .param j => one (named.getD j []) i
      | .va => one vaArg i
    let more ← substFrom Γ n whole bs (i + 1) named vaArg
    return here ++ more
where
  one (a : List Tok) (i : Nat) : Option (List RTok) :=
    if adjacentPaste whole i then some (if a.isEmpty then [RTok.pm] else a.map RTok.t)
    else (expand Γ n a).map (·.map RTok.t)
end

end PP

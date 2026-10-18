/-
  PR terms, and their translation into macros (pp_primrec.tex, Theorem 10): each node its
  own macro, its helpers fresh -- named after the node's path.
-/
import Read

namespace PP

/-- Primitive recursive terms, with their arity. -/
inductive Term where
  | zero (k : Nat)
  | succ
  | proj (k i : Nat)
  | comp (k : Nat) (h : Term) (gs : List Term)
  | prec (f g : Term)
  deriving Repr, Inhabited

def Term.arity : Term → Nat
  | .zero k => k
  | .succ => 1
  | .proj k _ => k
  | .comp k _ _ => k
  | .prec f _ => f.arity + 1

/-- What a term computes. -/
def Term.eval : Term → List Nat → Nat
  | .zero _, _ => 0
  | .succ, xs => xs.headD 0 + 1
  | .proj _ i, xs => xs.getD i 0
  | .comp _ h gs, xs => h.eval (gs.attach.map fun ⟨g, _⟩ => g.eval xs)
  | .prec f g, xs =>
    let ys := xs.tail
    Nat.rec (motive := fun _ => Nat) (f.eval ys) (fun c v => g.eval (c :: v :: ys)) (xs.headD 0)

def params (k : Nat) : List String := (List.range k).map fun i => s!"x{i}"
def commaJoin (l : List String) : String := ", ".intercalate l
/-- `, y1, ..., yk` -- nothing when there are none. -/
def tailArgs (l : List String) : String := String.join (l.map fun y => s!", {y}")

/-- The `#define`s of a term, its own macro named `p`. -/
def Term.defs : Term → String → List String
  | .zero _, p => [s!"#define {p}(...)"]
  | .succ, p => [s!"#define {p}(x0) x0 (~)"]
  | .proj k i, p => [s!"#define {p}({commaJoin (params k)}) x{i}"]
  | .comp k h gs, p =>
    let gnames := (List.range gs.length).map fun j => s!"{p}g{j}"
    let calls := gnames.map fun g => s!"{g}({commaJoin (params k)})"
    s!"#define {p}({commaJoin (params k)}) {p}h({commaJoin calls})" ::
      (h.defs s!"{p}h" ++ (gs.attach.zip gnames).flatMap fun (⟨g, _⟩, n) => g.defs n)
  | .prec f g, p =>
    let ys := (params f.arity).map fun y => s!"y{y}"
    [s!"#define {p}(n{tailArgs ys}) {p}SEL({p}ITER(n, ( , {p}f({commaJoin ys}){tailArgs ys} )))",
     s!"#define {p}SEL(t) {p}SEL2 t",
     s!"#define {p}SEL2(c, v, ...) v",
     s!"#define {p}TH(s) {p}STEP s",
     s!"#define {p}STEP(c, v{tailArgs ys}) ( c (~) , {p}g(c, v{tailArgs ys}){tailArgs ys} )",
     s!"#define {p}ITER(n, s) {p}CAT({p}GEN(n) s {p}BRA n, _END)",
     s!"#define {p}GEN(n) {p}CAT2({p}GA n, _END)",
     s!"#define {p}GA(...) {p}TH {p}D1() {p}GB",
     s!"#define {p}GB(...) {p}TH {p}D1() {p}GA",
     s!"#define {p}GA_END",
     s!"#define {p}GB_END",
     s!"#define {p}BRA(...) ) {p}BRB",
     s!"#define {p}BRB(...) ) {p}BRA",
     s!"#define {p}BRA_END",
     s!"#define {p}BRB_END",
     s!"#define {p}D1() {p}D0 {p}OUT()",
     s!"#define {p}D0() (",
     s!"#define {p}OUT",
     s!"#define {p}CAT(a, b) {p}CAT_(a, b)",
     s!"#define {p}CAT_(a, b) a##b",
     s!"#define {p}CAT2(a, b) {p}CAT2_(a, b)",
     s!"#define {p}CAT2_(a, b) a##b"] ++ f.defs s!"{p}f" ++ g.defs s!"{p}g"

def Term.env (t : Term) : Env := defines ("\n".intercalate (t.defs "T"))

def unary (n : Nat) : String := String.join (List.replicate n "(~)")
def callOf (t : Term) (xs : List Nat) : String := s!"T({commaJoin (xs.map unary)})"
def runTerm (t : Term) (fuel : Nat) (xs : List Nat) : Option Nat := (run t.env fuel (callOf t xs)).map groups

/-! Examples: addition, multiplication, predecessor, truncated subtraction, 2^n. -/
-- add(n, y) = rec: f(y) = y, g(c, v, y) = v + 1
def addT : Term := .prec (.proj 1 0) (.comp 3 .succ [.proj 3 1])
-- mul(n, y) = rec: f(y) = 0, g(c, v, y) = add(y, v)
def mulT : Term := .prec (.zero 1) (.comp 3 addT [.proj 3 2, .proj 3 1])
-- pred(n) = rec: f() = 0, g(c, v) = c
def predT : Term := .prec (.zero 0) (.proj 2 0)
-- sub(n, y) = y - n: rec over n: f(y) = y, g(c, v, y) = pred(v)
def subT : Term := .prec (.proj 1 0) (.comp 3 predT [.proj 3 1])
-- exp2(n) = rec: f() = 1, g(c, v) = add(v, v)
def exp2T : Term := .prec (.comp 0 .succ [.zero 0]) (.comp 2 addT [.proj 2 1, .proj 2 1])

end PP

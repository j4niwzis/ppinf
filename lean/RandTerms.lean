import TransEnv
open PP
-- a small LCG
def nextR (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

/-- A random well-formed term of arity `k`, depth at most `d`. -/
partial def gen (s : Nat) (k d : Nat) : Term × Nat :=
  let s := nextR s
  let r := s % 10
  if d == 0 || r < 3 then
    let s := nextR s
    match s % 3 with
    | 0 => (.zero k, s)
    | 1 => if k == 0 then (.zero 0, s) else (.proj k (s / 7 % k), s)
    | _ => if k == 1 then (.succ, s) else if k == 0 then (.comp 0 .succ [.zero 0], s) else (.comp k .succ [.proj k (s / 7 % k)], s)
  else if r < 6 && k ≥ 1 then
    -- prec: f of arity k-1, g of arity k+1
    let (f, s) := gen s (k - 1) (d - 1)
    let (g, s) := gen s (k + 1) (d - 1)
    (.prec f g, s)
  else
    let s := nextR s
    let m := s % 3
    let (h, s) := gen s m (d - 1)
    let rec gs (s : Nat) : Nat → List Term × Nat
      | 0 => ([], s)
      | j + 1 => let (g, s) := gen s k (d - 1); let (rest, s) := gs s j; (g :: rest, s)
    let (l, s) := gs s m
    (.comp k h l, s)

def evalCapped (t : Term) (xs : List Nat) : Nat := t.eval xs

def runD (t : Term) (fuel : Nat) (xs : List Nat) : Option Nat :=
  (run (t.denv "T") fuel (callOf t xs)).map groups

def precs : Term → Nat
  | .prec f g => 1 + precs f + precs g
  | .comp _ h gs => precs h + (gs.attach.map fun ⟨g, _⟩ => precs g).sum
  | _ => 0

def nestedPrec : Term → Bool
  | .prec f g => precs f + precs g > 0 || nestedPrec f || nestedPrec g
  | .comp _ h gs => nestedPrec h || gs.attach.any fun ⟨g, _⟩ => nestedPrec g
  | _ => false

def check (seed : Nat) : Option String × Nat × Bool := Id.run do
  let (t, s) := gen seed 2 4
  let mut s := s
  let mut ran := 0
  for _ in [0:3] do
    s := nextR s
    let a := s % 3
    s := nextR s
    let b := s % 3
    let v := t.eval [a, b]
    if v ≤ 12 then
      ran := ran + 1
      match runD t 20000 [a, b] with
      | some w => if w != v then return (some s!"MISMATCH seed {seed} args {a},{b}: pp {w}, eval {v}: {repr t}", ran, nestedPrec t)
      | none => return (some s!"FAIL seed {seed} args {a},{b} (eval {v}): {repr t}", ran, nestedPrec t)
  return (none, ran, nestedPrec t && ran > 0)

#eval Id.run do
  let mut bad := #[]
  let mut runs := 0
  let mut nested := 0
  for i in [0:400] do
    let (m, r, n) := check (i * 7919 + 13)
    runs := runs + r
    if n then nested := nested + 1
    if let some m := m then bad := bad.push m
  return (bad.size, runs, nested, bad.toList.take 2)

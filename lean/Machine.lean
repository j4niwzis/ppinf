/-
  The scan as a first-order machine (for Theorem 9): one rewrite action per step, on an
  explicit stack of the macros whose bodies are being substituted.
-/
import Semantics

namespace PP

/-- A scan level: what it has emitted (reversed) and the input left. -/
structure Level where
  out : List Tok
  inp : List Tok
  deriving Inhabited

/-- A macro whose body is being substituted: the level it suspended (its input is what follows
    the call), the step it makes, the body's elements left and their index, the replacement so
    far, and the arguments. -/
structure Frame where
  lvl : Level
  step : Step
  whole : List BTok
  bs : List BTok
  i : Nat
  acc : List RTok
  named : List (List Tok)
  va : List Tok
  deriving Inhabited

/-- The machine: scanning `cur` under `fs`, placing the top frame's body, or stopped. -/
inductive Mode where
  | scan (cur : Level) (fs : List Frame)
  | body (f : Frame) (fs : List Frame)
  | done (out : List Tok)
  | fail
  deriving Inhabited

structure MState where
  mode : Mode
  steps : List Step
  c : Nat
  deriving Inhabited

def Frame.start (lvl : Level) (step : Step) (body : List BTok) (named : List (List Tok)) (va : List Tok) : Frame :=
  Frame.mk lvl step body body 0 [] named va

/-- A macro opened: its frame on top, the counter past its step. -/
def openM (st : MState) (fs : List Frame) (f : Frame) : MState := MState.mk (.body f fs) st.steps (st.c + 1)

/-- One action. -/
def mstep (Γ : Env) (st : MState) : MState :=
  match st.mode with
  | .done _ | .fail => st
  | .scan ⟨out, []⟩ [] => { st with mode := .done out.reverse }
  | .scan ⟨out, []⟩ (f :: fs) =>
    let f' : Frame := { f with bs := f.bs.tail, i := f.i + 1, acc := f.acc ++ (finalize out.reverse).map RTok.t }
    { st with mode := .body f' fs }
  | .scan ⟨out, x :: rest⟩ fs =>
    let emitM := { st with mode := .scan ⟨x :: out, rest⟩ fs }
    if x.s ∈ x.H then emitM else
    match Γ.find x.s with
    | some (.obj body) =>
      openM st fs (Frame.start ⟨out, rest⟩ (Step.mk x.s x none (x.s :: x.H) st.c) body [] [])
    | some (.fn arity variadic body) =>
      match rest with
      | open_ :: after' =>
        if open_.s != "(" then emitM else
        match closeAt 0 after' [] with
        | none => { st with mode := .fail }
        | some (inner, cl, rest') =>
          match bind arity variadic inner with
          | none => { st with mode := .fail }
          | some (named, va) =>
            openM st fs (Frame.start ⟨out, rest'⟩ (Step.mk x.s x (some cl) (x.s :: inter x.H cl.H) st.c) body named va)
      | [] => emitM
    | none => emitM
  | .body f fs =>
    match f.bs with
    | [] =>
      match paste f.acc with
      | none => { st with mode := .fail }
      | some b =>
        { st with mode := .scan ⟨f.lvl.out, mark f.step.id f.step.mark b ++ f.lvl.inp⟩ fs,
                  steps := f.step :: st.steps }
    | b :: bs =>
      let place (xs : List RTok) : MState :=
        let f' : Frame := { f with bs := bs, i := f.i + 1, acc := f.acc ++ xs }
        { st with mode := .body f' fs }
      let arg (a : List Tok) : MState :=
        if adjacentPaste f.whole f.i then place (if a.isEmpty then [RTok.pm] else a.map RTok.t)
        else { st with mode := .scan ⟨[], a⟩ (f :: fs) }
      match b with
      | .tok s => place [RTok.t { s }]
      | .paste => place [RTok.op]
      | .param j => arg (f.named.getD j [])
      | .va => arg f.va

def mrun (Γ : Env) : Nat → MState → MState
  | 0, st => st
  | k + 1, st => mrun Γ k (mstep Γ st)

/-- The machine's answer, as `expand` gives it: output, steps in order, next number. -/
def mexpand (Γ : Env) (k c : Nat) (xs : List Tok) : Option (List Tok × List Step × Nat) :=
  let st := mrun Γ k { mode := .scan ⟨[], xs⟩ [], steps := [], c }
  match st.mode with
  | .done out => some (finalize out, st.steps.reverse, st.c)
  | _ => none

/-- How many actions a scan of fuel `n` may take, `b` the longest body. -/
def mcost (b : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (b + 1) * mcost b n + 2 * b + 3

end PP

/-
  Theorem 9: the machine's step, split into one function per case -- each small enough to be
  shown primitive recursive on its own.
-/
import Machine

namespace PP

def emitM (st : MState) (out : List Tok) (x : Tok) (rest : List Tok) (fs : List Frame) : MState :=
  { st with mode := .scan ⟨x :: out, rest⟩ fs }

/-- A function-like macro's name: its arguments read, its frame opened. -/
def fnOpenM (st : MState) (out : List Tok) (x : Tok) (fs : List Frame) (arity : Nat) (variadic : Bool)
    (body : List BTok) (after' : List Tok) : MState :=
  match closeAt 0 after' [] with
  | none => { st with mode := .fail }
  | some (inner, cl, rest') =>
    match bind arity variadic inner with
    | none => { st with mode := .fail }
    | some (named, va) =>
      openM st fs (Frame.start ⟨out, rest'⟩ (Step.mk x.s x (some cl) (x.s :: inter x.H cl.H) st.c) body named va)

def fnStepM (st : MState) (out : List Tok) (x : Tok) (rest : List Tok) (fs : List Frame) (arity : Nat)
    (variadic : Bool) (body : List BTok) : MState :=
  match rest with
  | open_ :: after' => if open_.s != "(" then emitM st out x rest fs else fnOpenM st out x fs arity variadic body after'
  | [] => emitM st out x rest fs

def defStepM (st : MState) (out : List Tok) (x : Tok) (rest : List Tok) (fs : List Frame) : Option Def → MState
  | some (.obj body) => openM st fs (Frame.start ⟨out, rest⟩ (Step.mk x.s x none (x.s :: x.H) st.c) body [] [])
  | some (.fn arity variadic body) => fnStepM st out x rest fs arity variadic body
  | none => emitM st out x rest fs

def consStepM (Γ : Env) (st : MState) (out : List Tok) (x : Tok) (rest : List Tok) (fs : List Frame) : MState :=
  if x.s ∈ x.H then emitM st out x rest fs else defStepM st out x rest fs (Γ.find x.s)

/-- A level's input used up: the run ends, or an argument is done. -/
def endStepM (st : MState) (out : List Tok) : List Frame → MState
  | [] => { st with mode := .done out.reverse }
  | f :: fs =>
    { st with mode := .body { f with bs := f.bs.tail, i := f.i + 1, acc := f.acc ++ (finalize out.reverse).map RTok.t } fs }

/-- A body done: pasted, marked, put in front of what followed the call. -/
def closeM (st : MState) (f : Frame) (fs : List Frame) : MState :=
  match paste f.acc with
  | none => { st with mode := .fail }
  | some b => { st with mode := .scan ⟨f.lvl.out, mark f.step.id f.step.mark b ++ f.lvl.inp⟩ fs, steps := f.step :: st.steps }

def placeM (st : MState) (f : Frame) (bs : List BTok) (fs : List Frame) (xs : List RTok) : MState :=
  { st with mode := .body { f with bs := bs, i := f.i + 1, acc := f.acc ++ xs } fs }

def argM (st : MState) (f : Frame) (bs : List BTok) (fs : List Frame) (a : List Tok) : MState :=
  if adjacentPaste f.whole f.i then placeM st f bs fs (if a.isEmpty then [RTok.pm] else a.map RTok.t)
  else { st with mode := .scan ⟨[], a⟩ (f :: fs) }

def elemM (st : MState) (f : Frame) (bs : List BTok) (fs : List Frame) : BTok → MState
  | .tok s => placeM st f bs fs [RTok.t { s }]
  | .paste => placeM st f bs fs [RTok.op]
  | .param j => argM st f bs fs (f.named.getD j [])
  | .va => argM st f bs fs f.va

def bodyStepM (st : MState) (f : Frame) (fs : List Frame) : MState :=
  match f.bs with
  | [] => closeM st f fs
  | b :: bs => elemM st f bs fs b

def mstep2 (Γ : Env) (st : MState) : MState :=
  match st.mode with
  | .done _ | .fail => st
  | .scan ⟨out, []⟩ fs => endStepM st out fs
  | .scan ⟨out, x :: rest⟩ fs => consStepM Γ st out x rest fs
  | .body f fs => bodyStepM st f fs

theorem mstep2_eq (Γ : Env) (st : MState) : mstep2 Γ st = mstep Γ st := by
  rcases st with ⟨m, steps, c⟩
  cases m with
  | scan cur fs =>
    rcases cur with ⟨out, _ | ⟨x, rest⟩⟩
    · cases fs <;> rfl
    · simp only [mstep2, mstep, consStepM]
      split
      · rfl
      · rename_i h
        cases hf : Γ.find x.s with
        | none => simp [defStepM, hf, emitM]
        | some d =>
          cases d with
          | obj body => simp [defStepM, hf]
          | fn arity variadic body =>
            simp only [defStepM, hf, fnStepM]
            cases rest with
            | nil => rfl
            | cons open_ after' =>
              simp only
              split
              · rfl
              · simp only [fnOpenM]
                cases hc : closeAt 0 after' [] with
                | none => simp
                | some t =>
                  obtain ⟨inner, cl, rest'⟩ := t
                  cases hb : bind arity variadic inner with
                  | none => simp [hb]
                  | some u => obtain ⟨named, va⟩ := u; simp [hb]
  | body f fs =>
    simp only [mstep2, mstep, bodyStepM]
    cases f.bs with
    | nil => simp only [closeM]; cases hp : paste f.acc <;> simp
    | cons b bs => cases b <;> rfl
  | done out => rfl
  | fail => rfl

end PP

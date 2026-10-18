/-
  Theorem 9: the machine's step is primitive recursive, case by case (MachineSplit), and so
  is running it any number of times.
-/
import PrimPaste

open Primrec

namespace PP

variable {α : Type} [Primcodable α]

/-! The state's constructors and fields. -/

theorem mstate_mk {m : α → Mode} {s : α → List Step} {c : α → ℕ} (hm : Primrec m) (hs : Primrec s) (hc : Primrec c) :
    Primrec fun a => MState.mk (m a) (s a) (c a) :=
  ((of_equiv_symm (e := mstateEquiv)).comp (hm.pair (hs.pair hc))).of_eq fun _ => rfl
theorem mstate_mode : Primrec MState.mode := (fst.comp (of_equiv (e := mstateEquiv))).of_eq fun _ => rfl
theorem mstate_steps : Primrec MState.steps := (fst.comp (snd.comp (of_equiv (e := mstateEquiv)))).of_eq fun _ => rfl
theorem mstate_c : Primrec MState.c := (snd.comp (snd.comp (of_equiv (e := mstateEquiv)))).of_eq fun _ => rfl

theorem mode_scan {l : α → Level} {fs : α → List Frame} (hl : Primrec l) (hfs : Primrec fs) :
    Primrec fun a => Mode.scan (l a) (fs a) :=
  ((of_equiv_symm (e := modeEquiv)).comp (sumInl.comp (hl.pair hfs))).of_eq fun _ => rfl
theorem mode_body {f : α → Frame} {fs : α → List Frame} (hf : Primrec f) (hfs : Primrec fs) :
    Primrec fun a => Mode.body (f a) (fs a) :=
  ((of_equiv_symm (e := modeEquiv)).comp (sumInr.comp (sumInl.comp (hf.pair hfs)))).of_eq fun _ => rfl
theorem mode_done {o : α → List Tok} (ho : Primrec o) : Primrec fun a => Mode.done (o a) :=
  ((of_equiv_symm (e := modeEquiv)).comp (sumInr.comp (sumInr.comp (option_some.comp ho)))).of_eq fun _ => rfl

theorem frame_lvl : Primrec Frame.lvl := (fst.comp (of_equiv (e := frameEquiv))).of_eq fun _ => rfl
theorem frame_step : Primrec Frame.step := (fst.comp (snd.comp (of_equiv (e := frameEquiv)))).of_eq fun _ => rfl
theorem frame_whole : Primrec Frame.whole := (fst.comp (snd.comp (snd.comp (of_equiv (e := frameEquiv))))).of_eq fun _ => rfl
theorem frame_bs : Primrec Frame.bs :=
  (fst.comp (snd.comp (snd.comp (snd.comp (of_equiv (e := frameEquiv)))))).of_eq fun _ => rfl
theorem frame_i : Primrec Frame.i :=
  (fst.comp (snd.comp (snd.comp (snd.comp (snd.comp (of_equiv (e := frameEquiv))))))).of_eq fun _ => rfl
theorem frame_acc : Primrec Frame.acc :=
  (fst.comp (snd.comp (snd.comp (snd.comp (snd.comp (snd.comp (of_equiv (e := frameEquiv)))))))).of_eq fun _ => rfl
theorem frame_named : Primrec Frame.named :=
  (fst.comp (snd.comp (snd.comp (snd.comp (snd.comp (snd.comp (snd.comp (of_equiv (e := frameEquiv))))))))).of_eq
    fun _ => rfl
theorem frame_va : Primrec Frame.va :=
  (snd.comp (snd.comp (snd.comp (snd.comp (snd.comp (snd.comp (snd.comp (of_equiv (e := frameEquiv))))))))).of_eq
    fun _ => rfl
theorem frame_mk {l : α → Level} {st : α → Step} {w b : α → List BTok} {i : α → ℕ} {ac : α → List RTok}
    {nm : α → List (List Tok)} {v : α → List Tok} (hl : Primrec l) (hst : Primrec st) (hw : Primrec w) (hb : Primrec b)
    (hi : Primrec i) (hac : Primrec ac) (hnm : Primrec nm) (hv : Primrec v) :
    Primrec fun a => Frame.mk (l a) (st a) (w a) (b a) (i a) (ac a) (nm a) (v a) :=
  ((of_equiv_symm (e := frameEquiv)).comp
    (hl.pair (hst.pair (hw.pair (hb.pair (hi.pair (hac.pair (hnm.pair hv)))))))).of_eq fun _ => rfl

/-! The cases. -/

theorem emitM_prim {st : α → MState} {out rest : α → List Tok} {x : α → Tok} {fs : α → List Frame}
    (hst : Primrec st) (hout : Primrec out) (hx : Primrec x) (hrest : Primrec rest) (hfs : Primrec fs) :
    Primrec fun a => emitM (st a) (out a) (x a) (rest a) (fs a) :=
  (mstate_mk (mode_scan (level_mk (list_cons.comp hx hout) hrest) hfs) (mstate_steps.comp hst)
    (mstate_c.comp hst)).of_eq fun _ => rfl

theorem fail_prim {st : α → MState} (hst : Primrec st) : Primrec fun a => { st a with mode := Mode.fail } :=
  (mstate_mk (const Mode.fail) (mstate_steps.comp hst) (mstate_c.comp hst)).of_eq fun _ => rfl

theorem openM_prim {st : α → MState} {fs : α → List Frame} {f : α → Frame}
    (hst : Primrec st) (hfs : Primrec fs) (hf : Primrec f) : Primrec fun a => openM (st a) (fs a) (f a) :=
  (mstate_mk (mode_body hf hfs) (mstate_steps.comp hst) (succ.comp (mstate_c.comp hst))).of_eq fun _ => rfl

theorem start_prim {l : α → Level} {st : α → Step} {b : α → List BTok} {nm : α → List (List Tok)} {v : α → List Tok}
    (hl : Primrec l) (hst : Primrec st) (hb : Primrec b) (hnm : Primrec nm) (hv : Primrec v) :
    Primrec fun a => Frame.start (l a) (st a) (b a) (nm a) (v a) :=
  (frame_mk hl hst hb hb (const 0) (const []) hnm hv).of_eq fun _ => rfl

/-- The arguments of `fnOpenM`, as one tuple. -/
abbrev FnArgs := MState × List Tok × Tok × List Frame × ℕ × Bool × List BTok × List Tok

theorem fnOpenM_prim : Primrec fun p : FnArgs => fnOpenM p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1
    p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2 := by
  have st : Primrec fun p : FnArgs => p.1 := fst
  have out : Primrec fun p : FnArgs => p.2.1 := fst.comp snd
  have x : Primrec fun p : FnArgs => p.2.2.1 := fst.comp (snd.comp snd)
  have fs : Primrec fun p : FnArgs => p.2.2.2.1 := fst.comp (snd.comp (snd.comp snd))
  have ar : Primrec fun p : FnArgs => p.2.2.2.2.1 := fst.comp (snd.comp (snd.comp (snd.comp snd)))
  have vr : Primrec fun p : FnArgs => p.2.2.2.2.2.1 := fst.comp (snd.comp (snd.comp (snd.comp (snd.comp snd))))
  have body : Primrec fun p : FnArgs => p.2.2.2.2.2.2.1 :=
    fst.comp (snd.comp (snd.comp (snd.comp (snd.comp (snd.comp snd)))))
  have aft : Primrec fun p : FnArgs => p.2.2.2.2.2.2.2 := snd.comp (snd.comp (snd.comp (snd.comp (snd.comp (snd.comp snd)))))
  -- r : (FnArgs × (inner, cl, rest')) × (named, va)
  have opened : Primrec fun r : (FnArgs × (List Tok × Tok × List Tok)) × (List (List Tok) × List Tok) =>
      openM r.1.1.1 r.1.1.2.2.2.1 (Frame.start ⟨r.1.1.2.1, r.1.2.2.2⟩
        (Step.mk r.1.1.2.2.1.s r.1.1.2.2.1 (some r.1.2.2.1) (r.1.1.2.2.1.s :: inter r.1.1.2.2.1.H r.1.2.2.1.H) r.1.1.1.c)
        r.1.1.2.2.2.2.2.2.1 r.2.1 r.2.2) :=
    openM_prim (st.comp (fst.comp fst)) (fs.comp (fst.comp fst))
      (start_prim (level_mk (out.comp (fst.comp fst)) (snd.comp (snd.comp (snd.comp fst))))
        (step_mk (tok_s.comp (x.comp (fst.comp fst))) (x.comp (fst.comp fst)) (option_some.comp (fst.comp (snd.comp (snd.comp fst))))
          (list_cons.comp (tok_s.comp (x.comp (fst.comp fst)))
            (inter_prim.comp (tok_H.comp (x.comp (fst.comp fst))) (tok_H.comp (fst.comp (snd.comp (snd.comp fst))))))
          (mstate_c.comp (st.comp (fst.comp fst))))
        (body.comp (fst.comp fst)) (fst.comp snd) (snd.comp snd))
  have found : Primrec fun q : FnArgs × (List Tok × Tok × List Tok) =>
      Option.casesOn (motive := fun _ => MState) (bind q.1.2.2.2.2.1 q.1.2.2.2.2.2.1 q.2.1) { q.1.1 with mode := Mode.fail } fun u =>
        openM q.1.1 q.1.2.2.2.1 (Frame.start ⟨q.1.2.1, q.2.2.2⟩
          (Step.mk q.1.2.2.1.s q.1.2.2.1 (some q.2.2.1) (q.1.2.2.1.s :: inter q.1.2.2.1.H q.2.2.1.H) q.1.1.c)
          q.1.2.2.2.2.2.2.1 u.1 u.2) :=
    option_casesOn (bind_prim.comp (pair (pair (ar.comp fst) (vr.comp fst)) (fst.comp snd))) (fail_prim (st.comp fst))
      opened.to₂
  refine (option_casesOn (closeAt_prim.comp aft) (fail_prim st) found.to₂).of_eq fun p => ?_
  unfold fnOpenM
  cases hc : closeAt 0 p.2.2.2.2.2.2.2 [] with
  | none => rfl
  | some t =>
    obtain ⟨inner, cl, rest'⟩ := t
    simp only
    cases hb : bind p.2.2.2.2.1 p.2.2.2.2.2.1 inner with
    | none => rfl
    | some u => rfl

theorem fnOpenM_c {st : α → MState} {out aft : α → List Tok} {x : α → Tok} {fs : α → List Frame} {ar : α → ℕ}
    {vr : α → Bool} {body : α → List BTok} (hst : Primrec st) (hout : Primrec out) (hx : Primrec x) (hfs : Primrec fs)
    (har : Primrec ar) (hvr : Primrec vr) (hbody : Primrec body) (haft : Primrec aft) :
    Primrec fun a => fnOpenM (st a) (out a) (x a) (fs a) (ar a) (vr a) (body a) (aft a) :=
  (fnOpenM_prim.comp (hst.pair (hout.pair (hx.pair (hfs.pair (har.pair (hvr.pair (hbody.pair haft)))))))).of_eq
    fun _ => rfl

theorem fnStepM_prim {st : α → MState} {out rest : α → List Tok} {x : α → Tok} {fs : α → List Frame} {ar : α → ℕ}
    {vr : α → Bool} {body : α → List BTok} (hst : Primrec st) (hout : Primrec out) (hx : Primrec x)
    (hrest : Primrec rest) (hfs : Primrec fs) (har : Primrec ar) (hvr : Primrec vr) (hbody : Primrec body) :
    Primrec fun a => fnStepM (st a) (out a) (x a) (rest a) (fs a) (ar a) (vr a) (body a) := by
  have e := emitM_prim hst hout hx hrest hfs
  have e' : Primrec fun q : α × (Tok × List Tok) => emitM (st q.1) (out q.1) (x q.1) (rest q.1) (fs q.1) :=
    emitM_prim (hst.comp fst) (hout.comp fst) (hx.comp fst) (hrest.comp fst) (hfs.comp fst)
  have o : Primrec fun q : α × (Tok × List Tok) =>
      fnOpenM (st q.1) (out q.1) (x q.1) (fs q.1) (ar q.1) (vr q.1) (body q.1) q.2.2 := fnOpenM_c (hst.comp fst) (hout.comp fst) (hx.comp fst) (hfs.comp fst) (har.comp fst) (hvr.comp fst)
    (hbody.comp fst) (snd.comp snd)
  refine (list_casesOn hrest e
    (ite_bool (Primrec.not.comp (beq_prim.comp (tok_s.comp (fst.comp snd)) (const "("))) e' o).to₂).of_eq fun a => ?_
  unfold fnStepM
  cases h : rest a with
  | nil => rfl
  | cons o r => simp [h, bne]

theorem defStepM_prim {st : α → MState} {out rest : α → List Tok} {x : α → Tok} {fs : α → List Frame}
    {od : α → Option Def} (hst : Primrec st) (hout : Primrec out) (hx : Primrec x) (hrest : Primrec rest)
    (hfs : Primrec fs) (hod : Primrec od) :
    Primrec fun a => defStepM (st a) (out a) (x a) (rest a) (fs a) (od a) := by
  -- inside: r : α × Def, then the sum's cases
  have objB : Primrec fun q : (α × Def) × List BTok =>
      openM (st q.1.1) (fs q.1.1) (Frame.start ⟨out q.1.1, rest q.1.1⟩
        (Step.mk (x q.1.1).s (x q.1.1) none ((x q.1.1).s :: (x q.1.1).H) (st q.1.1).c) q.2 [] []) :=
    openM_prim (hst.comp (fst.comp fst)) (hfs.comp (fst.comp fst))
      (start_prim (level_mk (hout.comp (fst.comp fst)) (hrest.comp (fst.comp fst)))
        (step_mk (tok_s.comp (hx.comp (fst.comp fst))) (hx.comp (fst.comp fst)) (const none)
          (list_cons.comp (tok_s.comp (hx.comp (fst.comp fst))) (tok_H.comp (hx.comp (fst.comp fst))))
          (mstate_c.comp (hst.comp (fst.comp fst))))
        snd (const []) (const []))
  have fnB : Primrec fun q : (α × Def) × (ℕ × Bool × List BTok) =>
      fnStepM (st q.1.1) (out q.1.1) (x q.1.1) (rest q.1.1) (fs q.1.1) q.2.1 q.2.2.1 q.2.2.2 :=
    fnStepM_prim (hst.comp (fst.comp fst)) (hout.comp (fst.comp fst)) (hx.comp (fst.comp fst)) (hrest.comp (fst.comp fst))
      (hfs.comp (fst.comp fst)) (fst.comp snd) (fst.comp (snd.comp snd)) (snd.comp (snd.comp snd))
  have someB : Primrec fun r : α × Def => defStepM (st r.1) (out r.1) (x r.1) (rest r.1) (fs r.1) (some r.2) :=
    (sumCasesOn ((of_equiv (e := defEquiv)).comp snd) objB.to₂ fnB.to₂).of_eq fun r => by
      rcases r with ⟨a, _ | _⟩ <;> rfl
  exact (option_casesOn hod (emitM_prim hst hout hx hrest hfs) someB.to₂).of_eq fun a => by
    cases od a <;> rfl

theorem consStepM_prim (Γ : Env) {st : α → MState} {out rest : α → List Tok} {x : α → Tok} {fs : α → List Frame}
    (hst : Primrec st) (hout : Primrec out) (hx : Primrec x) (hrest : Primrec rest) (hfs : Primrec fs) :
    Primrec fun a => consStepM Γ (st a) (out a) (x a) (rest a) (fs a) :=
  (Primrec.ite (mem_prim.comp (tok_s.comp hx) (tok_H.comp hx)) (emitM_prim hst hout hx hrest hfs)
    (defStepM_prim hst hout hx hrest hfs ((find_prim Γ).comp (tok_s.comp hx)))).of_eq fun a => rfl

theorem endStepM_prim {st : α → MState} {out : α → List Tok} {fs : α → List Frame}
    (hst : Primrec st) (hout : Primrec out) (hfs : Primrec fs) : Primrec fun a => endStepM (st a) (out a) (fs a) := by
  have done := mstate_mk (mode_done (list_reverse.comp hout)) (mstate_steps.comp hst) (mstate_c.comp hst)
  have f : Primrec fun q : α × Frame × List Frame => q.2.1 := fst.comp snd
  have more : Primrec fun q : α × Frame × List Frame =>
      MState.mk (Mode.body (Frame.mk q.2.1.lvl q.2.1.step q.2.1.whole q.2.1.bs.tail (q.2.1.i + 1)
        (q.2.1.acc ++ (finalize (out q.1).reverse).map RTok.t) q.2.1.named q.2.1.va) q.2.2) (st q.1).steps (st q.1).c :=
    mstate_mk (mode_body (frame_mk (frame_lvl.comp f) (frame_step.comp f) (frame_whole.comp f)
      (list_tail.comp (frame_bs.comp f)) (succ.comp (frame_i.comp f))
      (list_append.comp (frame_acc.comp f) (list_map (finalize_prim.comp (list_reverse.comp (hout.comp fst)))
        (rtok_t snd).to₂))
      (frame_named.comp f) (frame_va.comp f)) (snd.comp snd)) (mstate_steps.comp (hst.comp fst)) (mstate_c.comp (hst.comp fst))
  exact (list_casesOn hfs done more.to₂).of_eq fun a => by cases fs a <;> rfl

theorem closeM_prim {st : α → MState} {f : α → Frame} {fs : α → List Frame}
    (hst : Primrec st) (hf : Primrec f) (hfs : Primrec fs) : Primrec fun a => closeM (st a) (f a) (fs a) := by
  have go : Primrec fun q : α × List Tok =>
      MState.mk (Mode.scan ⟨(f q.1).lvl.out, mark (f q.1).step.id (f q.1).step.mark q.2 ++ (f q.1).lvl.inp⟩ (fs q.1))
        ((f q.1).step :: (st q.1).steps) (st q.1).c :=
    mstate_mk (mode_scan (level_mk (level_out.comp (frame_lvl.comp (hf.comp fst)))
        (list_append.comp (mark_prim.comp (pair (step_id.comp (frame_step.comp (hf.comp fst)))
          (pair (step_mark.comp (frame_step.comp (hf.comp fst))) snd)))
          (level_inp.comp (frame_lvl.comp (hf.comp fst))))) (hfs.comp fst))
      (list_cons.comp (frame_step.comp (hf.comp fst)) (mstate_steps.comp (hst.comp fst))) (mstate_c.comp (hst.comp fst))
  exact (option_casesOn (paste_prim.comp (frame_acc.comp hf)) (fail_prim hst) go.to₂).of_eq fun a => by
    unfold closeM; cases paste (f a).acc <;> rfl

theorem placeM_prim {st : α → MState} {f : α → Frame} {bs : α → List BTok} {fs : α → List Frame} {xs : α → List RTok}
    (hst : Primrec st) (hf : Primrec f) (hbs : Primrec bs) (hfs : Primrec fs) (hxs : Primrec xs) :
    Primrec fun a => placeM (st a) (f a) (bs a) (fs a) (xs a) :=
  (mstate_mk (mode_body (frame_mk (frame_lvl.comp hf) (frame_step.comp hf) (frame_whole.comp hf) hbs
      (succ.comp (frame_i.comp hf)) (list_append.comp (frame_acc.comp hf) hxs) (frame_named.comp hf) (frame_va.comp hf)) hfs)
    (mstate_steps.comp hst) (mstate_c.comp hst)).of_eq fun _ => rfl

theorem argM_prim {st : α → MState} {f : α → Frame} {bs : α → List BTok} {fs : α → List Frame} {ar : α → List Tok}
    (hst : Primrec st) (hf : Primrec f) (hbs : Primrec bs) (hfs : Primrec fs) (har : Primrec ar) :
    Primrec fun a => argM (st a) (f a) (bs a) (fs a) (ar a) :=
  (ite_bool (adjacentPaste_prim.comp (frame_whole.comp hf) (frame_i.comp hf))
    (placeM_prim hst hf hbs hfs (ite_bool (list_isEmpty.comp har) (const [RTok.pm]) (list_map har (rtok_t snd).to₂)))
    (mstate_mk (mode_scan (level_mk (const []) har) (list_cons.comp hf hfs)) (mstate_steps.comp hst)
      (mstate_c.comp hst))).of_eq fun a => by unfold argM; rfl

theorem elemM_prim {st : α → MState} {f : α → Frame} {bs : α → List BTok} {fs : α → List Frame} {b : α → BTok}
    (hst : Primrec st) (hf : Primrec f) (hbs : Primrec bs) (hfs : Primrec fs) (hb : Primrec b) :
    Primrec fun a => elemM (st a) (f a) (bs a) (fs a) (b a) := by
  have c1 := placeM_prim (hst.comp fst) (hf.comp fst) (hbs.comp fst) (hfs.comp fst)
    (list_cons.comp (rtok_t (tok_mk snd (const []) (const 0) (const []))) (const []))
  have c2 := argM_prim (hst.comp fst) (hf.comp fst) (hbs.comp fst) (hfs.comp fst)
    ((list_getD []).comp (frame_named.comp (hf.comp fst)) snd)
  have c3 : Primrec fun q : α × Bool =>
      if q.2 = true then argM (st q.1) (f q.1) (bs q.1) (fs q.1) (f q.1).va else placeM (st q.1) (f q.1) (bs q.1) (fs q.1) [RTok.op] :=
    ite_bool snd (argM_prim (hst.comp fst) (hf.comp fst) (hbs.comp fst) (hfs.comp fst) (frame_va.comp (hf.comp fst)))
      (placeM_prim (hst.comp fst) (hf.comp fst) (hbs.comp fst) (hfs.comp fst) (const [RTok.op]))
  have inner : Primrec fun q : α × (ℕ ⊕ Bool) =>
      Sum.casesOn (motive := fun _ => MState) q.2 (fun j => argM (st q.1) (f q.1) (bs q.1) (fs q.1) ((f q.1).named.getD j []))
        (fun t => if t = true then argM (st q.1) (f q.1) (bs q.1) (fs q.1) (f q.1).va
          else placeM (st q.1) (f q.1) (bs q.1) (fs q.1) [RTok.op]) :=
    sumCasesOn snd (c2.comp (pair (fst.comp fst) snd)).to₂ (c3.comp (pair (fst.comp fst) snd)).to₂
  exact (sumCasesOn ((of_equiv (e := btokEquiv)).comp hb) c1.to₂ inner.to₂).of_eq fun a => by
    cases h : b a with
    | va => rfl
    | paste => rfl
    | tok s => rfl
    | param j => rfl

theorem bodyStepM_prim {st : α → MState} {f : α → Frame} {fs : α → List Frame}
    (hst : Primrec st) (hf : Primrec f) (hfs : Primrec fs) : Primrec fun a => bodyStepM (st a) (f a) (fs a) :=
  (list_casesOn (frame_bs.comp hf) (closeM_prim hst hf hfs)
    (elemM_prim (hst.comp fst) (hf.comp fst) (snd.comp snd) (hfs.comp fst) (fst.comp snd)).to₂).of_eq fun a => by
    unfold bodyStepM; cases (f a).bs <;> rfl

/-- **The step is primitive recursive.** -/
theorem mstep_prim (Γ : Env) : Primrec (mstep Γ) := by
  have scanB : Primrec fun q : MState × (Level × List Frame) =>
      List.casesOn (motive := fun _ => MState) q.2.1.inp (endStepM q.1 q.2.1.out q.2.2)
        fun x rest => consStepM Γ q.1 q.2.1.out x rest q.2.2 :=
    list_casesOn (level_inp.comp (fst.comp snd)) (endStepM_prim fst (level_out.comp (fst.comp snd)) (snd.comp snd))
      (consStepM_prim Γ (fst.comp fst) (level_out.comp (fst.comp (snd.comp fst))) (fst.comp snd) (snd.comp snd)
        (snd.comp (snd.comp fst))).to₂
  have bodyB : Primrec fun q : MState × (Frame × List Frame) => bodyStepM q.1 q.2.1 q.2.2 :=
    bodyStepM_prim fst (fst.comp snd) (snd.comp snd)
  have inner : Primrec fun q : MState × ((Frame × List Frame) ⊕ Option (List Tok)) =>
      Sum.casesOn (motive := fun _ => MState) q.2 (fun p => bodyStepM q.1 p.1 p.2) (fun _ => q.1) :=
    sumCasesOn snd (bodyB.comp (pair (fst.comp fst) snd)).to₂ (fst.comp fst).to₂
  have h := sumCasesOn ((of_equiv (e := modeEquiv)).comp mstate_mode) scanB.to₂ inner.to₂
  refine h.of_eq fun st => ?_
  rw [← mstep2_eq]
  rcases st with ⟨m, steps, c⟩
  rcases m with ⟨⟨out, _ | ⟨x, rest⟩⟩, fs⟩ | ⟨f, fs⟩ | out | _ <;> rfl

theorem mrun_prim (Γ : Env) : Primrec₂ (mrun Γ) := by
  have h : Primrec fun p : ℕ × MState => (mstep Γ)^[p.1] p.2 := nat_iterate fst snd ((mstep_prim Γ).comp snd).to₂
  refine h.to₂.of_eq fun k st => ?_
  induction k generalizing st with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ, Function.comp]; exact ih _

end PP

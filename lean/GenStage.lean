/-
  Theorem 10, recursion, stage D: `GEN ( n̄ )` scans to `(TH ( )ⁿ`.
-/
import GenPrep

namespace PP

def mapQuad (f : Tok → Tok) (q : Tok × Tok × Tok × Tok) : Tok × Tok × Tok × Tok := (f q.1, f q.2.1, f q.2.2.1, f q.2.2.2)

theorem map_quadToks (f : Tok → Tok) : ∀ (Q : List (Tok × Tok × Tok × Tok)), (quadToks Q).map f = quadToks (Q.map (mapQuad f))
  | [] => rfl
  | q :: Q => by simp [quadToks, mapQuad] at *; exact map_quadToks f Q

/-- `CAT2_( (TH D0 ( ))ⁿ X , _END )` → `(TH ( )ⁿ`. -/
theorem cat2u_stage (Γ : Env) (hp : PunctFree Γ) {f g : Term} {π : List Code} (hR : Realizes Γ (.prec f g) π)
    {L : List Helper} (hL : ∀ y ∈ L, y ≠ .CAT2u ∧ y ≠ .TH ∧ y ≠ .D0 ∧ y ≠ .GAEND ∧ y ≠ .GBEND)
    {x lp sep rp e : Tok} {E1 : List Tok} {n : Nat} (hx : x.s = fullName π .CAT2u) (hxH : In π L x.H)
    (hlp : lp.s = "(") (hsep : sep.s = ",") (hrp : rp.s = ")") (hrpH : In π L rp.H)
    (hE1 : E1.map (·.s) = (List.replicate n [fullName π .TH, fullName π .D0, "(", ")"]).flatten ++
      [if n % 2 = 0 then fullName π .GA else fullName π .GB])
    (hE1H : ∀ t ∈ E1, In π L t.H) (he : e.s = "_END") (heH : In π L e.H) (c : Nat) :
    ∃ M o st c', scan Γ M c (callToks x lp sep rp [E1, [e]]) = some (o, st, c') ∧
      o.map (·.s) = (List.replicate n [fullName π .TH, "("]).flatten ∧ ∀ t ∈ o, t.s ∉ t.H := by
  obtain ⟨Q, X, rfl, hQl, hX, hQ⟩ := quad_split _ _ _ _ n E1 _ hE1
  have hnot : ∀ y, y ∉ L ∨ True := fun _ => Or.inr trivial
  have nL : ∀ y ∈ [Helper.CAT2u, .TH, .D0, .GAEND, .GBEND], y ∉ L := by
    intro y hy hyL; have := hL y hyL; simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl <;> simp_all
  -- the paste: `X ## _END`
  let XE : Helper := if n % 2 = 0 then .GAEND else .GBEND
  have hpaste : pasted X.s e.s = some (fullName π XE) := by
    rw [hX, he]; by_cases h : n % 2 = 0
    · simp only [h, ite_true, XE]; exact pasted_end π .GA .GAEND (by decide)
    · simp only [h, ite_false, XE]; exact pasted_end π .GB .GBEND (by decide)
  have hshape : ArgShape (quadToks Q ++ [X]) := by
    unfold ArgShape; rw [walk_spell, hE1]
    refine walkS_quads _ _ _ (fullName_ne_rp _ _) (fullName_ne_lp _ _) (fullName_ne_comma _ _) (fullName_ne_rp _ _)
      (fullName_ne_lp _ _) (fullName_ne_comma _ _) ?_ ?_ ?_ n <;> split <;>
      first | exact fullName_ne_rp _ _ | exact fullName_ne_lp _ _ | exact fullName_ne_comma _ _
  have heshape : ArgShape [e] := by
    unfold ArgShape; rw [walk_spell]; simp [walkS, he]
  -- after the paste: `(TH D0 ( ))ⁿ X_END`, marked
  let K := x.s :: inter x.H rp.H
  have hK : In π (.CAT2u :: L) K := by show In π (.CAT2u :: L) (x.s :: inter x.H rp.H); rw [hx]; exact in_mark hxH _ _
  have hd := d0stage Γ hp (L := .CAT2u :: L) (by simpa using fun h => nL .TH (by simp) h |>.elim)
    (by simpa using fun h => nL .D0 (by simp) h |>.elim) (find_prec hR .TH) (find_prec hR .D0)
    (xe := markOne c K { s := fullName π XE, H := inter X.H e.H })
    (by show Γ.find (fullName π XE) = _; simp only [XE]; split <;> exact find_prec hR _)
    (by
      apply not_mem_of_in (in_markOne hK (in_mono (fun y hy => by simp [hy]) (in_inter (hE1H X (by simp)) _)) c)
      simp only [XE]; split <;> simp <;> intro h <;> first | exact nL .GAEND (by simp) h | exact nL .GBEND (by simp) h)
    (Q.map (mapQuad (markOne c K))) (c + 1) ?_
  · obtain ⟨M, o, st, c', e1, ho, hfin⟩ := hd
    have e2 := paste_call Γ (by rw [hx]; exact find_prec hR .CAT2u)
      (by rw [hx]; exact not_mem_of_in hxH (nL .CAT2u (by simp))) hlp hsep hrp hshape heshape hpaste (rest := [])
      (n := M) (c := c) (q := (o, st, c')) (by rw [List.append_nil, mark_eq, List.map_append, map_quadToks]; exact e1)
    obtain ⟨st', e3⟩ := e2
    refine ⟨M + 1, o, st', c', ?_, by rw [ho, List.length_map, hQl], hfin⟩
    simpa [callToks] using e3
  · intro q hq
    obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
    obtain ⟨h1, h2, h3, h4⟩ := hQ q0 hq0
    have hin : ∀ t ∈ quadToks Q, In π (.CAT2u :: L) (markOne c K t).H := fun t ht =>
      in_markOne hK (in_mono (fun y hy => by simp [hy]) (hE1H t (by simp [ht]))) c
    have m1 : q0.1 ∈ quadToks Q := List.mem_flatMap.mpr ⟨q0, hq0, by simp⟩
    have m2 : q0.2.1 ∈ quadToks Q := List.mem_flatMap.mpr ⟨q0, hq0, by simp⟩
    have m4 : q0.2.2.2 ∈ quadToks Q := List.mem_flatMap.mpr ⟨q0, hq0, by simp⟩
    exact ⟨h1, h2, h3, h4, hin _ m1, hin _ m2, hin _ m4⟩

/-- The ping-pong output, finalized. -/
def PPOut (π : List Code) (n : Nat) (E : List Tok) : Prop :=
  E.map (·.s) = (List.replicate n [fullName π .TH, fullName π .D0, "(", ")"]).flatten ++
    [if n % 2 = 0 then fullName π .GA else fullName π .GB] ∧ ∀ t ∈ E, t.H = []

theorem toks_cat2 (π : List Code) (E1 E2 : List Tok) :
    toks (plainOut [nm π .CAT2u, tk "(", prm 0, tk ",", prm 1, tk ")"] [E1, E2]) =
      callToks { s := fullName π .CAT2u } { s := "(" } comma { s := ")" } [E1, E2] := by
  simp only [nm, tk, prm, plainOut, toks_t]
  rw [toks_map_t, toks_t, toks_map_t, toks_t]
  simp [toks, callToks, joinArgs, comma]

/-- `CAT2 ( GA n̄ , _END )` → `(TH ( )ⁿ`. -/
theorem cat2_stage (Γ : Env) (hp : PunctFree Γ) {f g : Term} {π : List Code} (hR : Realizes Γ (.prec f g) π)
    {L : List Helper} (hL : ∀ y ∈ L, y ≠ .CAT2 ∧ y ≠ .CAT2u ∧ y ≠ .GA ∧ y ≠ .GB ∧ y ≠ .TH ∧ y ≠ .D1 ∧ y ≠ .D0 ∧
      y ≠ .OUT ∧ y ≠ .GAEND ∧ y ≠ .GBEND)
    {x lp sep rp ga e : Tok} {Nm : List Tok} {n : Nat} (hx : x.s = fullName π .CAT2) (hxH : In π L x.H)
    (hlp : lp.s = "(") (hsep : sep.s = ",") (hrp : rp.s = ")") (hrpH : In π L rp.H)
    (hga : ga.s = fullName π .GA) (hgaH : In π L ga.H) (hN : IsNum Nm n) (hNH : ∀ t ∈ Nm, InJ π L t.H)
    (he : e.s = "_END") (heH : In π L e.H) (c : Nat) :
    ∃ M o st c', scan Γ M c (callToks x lp sep rp [ga :: Nm, [e]]) = some (o, st, c') ∧
      o.map (·.s) = (List.replicate n [fullName π .TH, "("]).flatten ∧ ∀ t ∈ o, t.s ∉ t.H := by
  let Ps : Nat → List Tok → Prop := fun j E => if j = 0 then PPOut π n E else if j = 1 then
    (E.map (·.s) = ["_END"] ∧ ∀ t ∈ E, t.H = []) else True
  have nCAT2 : Helper.CAT2 ∉ L := fun h => (hL _ h).1 rfl
  have nCAT2u : Helper.CAT2u ∉ L := fun h => (hL _ h).2.1 rfl
  have nGA : Helper.GA ∉ L := fun h => (hL _ h).2.2.1 rfl
  have nGB : Helper.GB ∉ L := fun h => (hL _ h).2.2.2.1 rfl
  have hdist : ∀ y ∈ [(ppNames hR).th, (ppNames hR).d1, (ppNames hR).d0, (ppNames hR).out, "(", ")"],
      y ≠ fullName π .GA ∧ y ≠ fullName π .GB := by
    intro y hy
    simp only [ppNames, List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨fullName_ne_helper (by decide), fullName_ne_helper (by decide)⟩
    · exact ⟨fullName_ne_helper (by decide), fullName_ne_helper (by decide)⟩
    · exact ⟨fullName_ne_helper (by decide), fullName_ne_helper (by decide)⟩
    · exact ⟨fullName_ne_helper (by decide), fullName_ne_helper (by decide)⟩
    · exact ⟨(fullName_ne_lp _ _).symm, (fullName_ne_lp _ _).symm⟩
    · exact ⟨(fullName_ne_rp _ _).symm, (fullName_ne_rp _ _).symm⟩
  have hargs : ∀ j, ExpandsP Γ ([ga :: Nm, [e]].getD j []) (Ps j) := by
    intro j c0
    match j with
    | 0 =>
      obtain ⟨G, hG, hGl, hGg⟩ := num_groups n Nm hN
      obtain ⟨Nf, o, st, c', e1, ho, hfin⟩ := pingpong Γ hp (ppNames hR) G (fullName π .GA) (fullName π .GB) ga c0
        (fun gr hgr => ⟨hGg gr hgr,
          not_mem_of_inJ (hNH gr.2.2 (by rw [hG]; exact List.mem_flatMap.mpr ⟨gr, hgr, by simp⟩)) nGA,
          not_mem_of_inJ (hNH gr.2.2 (by rw [hG]; exact List.mem_flatMap.mpr ⟨gr, hgr, by simp⟩)) nGB⟩)
        (find_prec hR .GA) (find_prec hR .GB) hdist (fullName_ne_helper (by decide)) hga
        (ppInv_of_in hR (fun y hy => let h := hL y hy; ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
          h.2.2.2.2.2.2.2.1⟩) hgaH .GA .GB (Or.inl rfl) (Or.inr rfl))
      refine ⟨Nf, finalize o, st, c', by simp [expand, hG, e1], ?_⟩
      simp only [Ps, ite_true]
      refine ⟨by rw [← hGl]; simpa [finalize, Function.comp_def, ppNames] using ho, finalize_H hfin⟩
    | 1 =>
      have hfree : NameFree Γ [e] := by intro t ht; simp at ht; subst ht; rw [he]; exact hp.2.2.2.2
      refine ⟨[e].length + 1, finalize [e], [], c0, by unfold expand; rw [show [ga :: Nm, [e]].getD 1 [] = [e] from rfl, scan_nameFree' hfree c0]; rfl, ?_⟩
      have hn : e.s ∉ e.H := by rw [he]; exact name_ne_of_in heH (fun π' y => fullName_ne_end π' y)
      simp only [Ps]
      refine ⟨by simp [finalize, he], fun t ht => ?_⟩
      simp [finalize] at ht; subst ht; simp [hn]
    | j + 2 =>
      refine ⟨1, [], [], c0, by simp [expand, scan, finalize], ?_⟩
      simp [Ps]
  have hs : ∀ A ∈ [ga :: Nm, [e]], ArgShape A := by
    intro A hA; simp at hA
    rcases hA with rfl | rfl
    · unfold ArgShape walk
      have h1 : (ga.s == ")") = false := by rw [hga]; simpa using fullName_ne_rp π .GA
      have h2 : (ga.s == "(") = false := by rw [hga]; simpa using fullName_ne_lp π .GA
      have h3 : (ga.s == ",") = false := by rw [hga]; simpa using fullName_ne_comma π .GA
      simp only [h1, h2, h3, Bool.false_eq_true, ite_false, Bool.false_and]
      exact walk_num hN 0
    · unfold ArgShape; rw [walk_spell]; simp [walkS, he]
  have hf : Γ.find x.s = some (.fn 2 false [nm π .CAT2u, tk "(", prm 0, tk ",", prm 1, tk ")"]) := by
    rw [hx]; exact find_prec hR .CAT2
  have hplain : Plain [nm π .CAT2u, tk "(", prm 0, tk ",", prm 1, tk ")"] := by
    intro b hb; simp [nm, tk, prm] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  obtain ⟨N, outs, c1, hos, hcall⟩ := call_plainP Γ hf (by rw [hx]; exact not_mem_of_in hxH nCAT2) hlp hsep hrp rfl
    (Or.inl (by decide)) hs Ps hargs hplain c
  have hpi : paramIdx [nm π .CAT2u, tk "(", prm 0, tk ",", prm 1, tk ")"] = [0, 1] := by simp [nm, tk, prm, paramIdx]
  rw [hpi] at hos
  obtain ⟨E1, E2, rfl, ⟨hP1, _⟩, ⟨hP2, _⟩⟩ : ∃ E1 E2, outs = [E1, E2] ∧ (Ps 0 E1 ∧ Fin E1) ∧ (Ps 1 E2 ∧ Fin E2) := by
    cases hos with
    | cons h1 hr => cases hr with
      | cons h2 hr' => cases hr'; exact ⟨_, _, rfl, h1, h2⟩
  simp only [Ps, ite_true, Nat.one_ne_zero, ite_false] at hP1 hP2
  obtain ⟨e2, rfl, he2⟩ : ∃ e2, E2 = [e2] ∧ e2.s = "_END" := by
    match E2, hP2.1 with
    | [e2], h => exact ⟨e2, rfl, by simpa using h⟩
    | [], h => simp at h
    | _ :: _ :: _, h => simp at h
  let K := x.s :: inter x.H rp.H
  have hK : In π (.CAT2 :: L) K := by show In π (.CAT2 :: L) (x.s :: inter x.H rp.H); rw [hx]; exact in_mark hxH _ _
  have hbody : ∀ s, In π (.CAT2 :: L) (markOne c K { s }).H := fun s => in_markOne hK (in_nil _ _) c
  obtain ⟨M, o, st, c', e1, ho, hfin⟩ := cat2u_stage Γ hp hR (L := .CAT2 :: L)
    (by
      intro y hy; simp at hy
      rcases hy with rfl | hy
      · decide
      · have h := hL y hy; exact ⟨h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩)
    (x := markOne c K { s := fullName π .CAT2u }) (lp := markOne c K { s := "(" }) (sep := markOne c K comma)
    (rp := markOne c K { s := ")" }) (e := markOne c K e2) (E1 := E1.map (markOne c K)) (n := n)
    rfl (hbody _) rfl rfl rfl (hbody _) (by simpa [Function.comp_def, markOne_s] using hP1.1)
    (by
      intro t ht; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
      exact in_markOne hK (in_of_nil (hP1.2 t0 ht0)) c)
    he2 (in_markOne hK (in_of_nil (hP2.2 e2 (by simp))) c) c1
  have e1' := scanMono Γ M c1 _ _ e1 (max N M) (Nat.le_max_right _ _)
  obtain ⟨st', hfin'⟩ := hcall (max N M) (Nat.le_max_left _ _) (o, st, c') (by
    rw [toks_cat2, mark_callToks]; exact e1')
  exact ⟨max N M + 1, o, st', c', hfin', ho, hfin⟩

theorem toks_gen (π : List Code) (o : List Tok) :
    toks (plainOut [nm π .CAT2, tk "(", nm π .GA, prm 0, tk ",", tk "_END", tk ")"] [o]) =
      callToks { s := fullName π .CAT2 } { s := "(" } comma { s := ")" } [{ s := fullName π .GA } :: o, [{ s := "_END" }]] := by
  simp only [nm, tk, prm, plainOut, toks_t]
  rw [toks_map_t]
  simp [toks, tokOf, callToks, joinArgs, comma]

/-- **`GEN ( n̄ )` → `(TH ( )ⁿ`.** -/
theorem gen_stage (Γ : Env) (hp : PunctFree Γ) {f g : Term} {π : List Code} (hR : Realizes Γ (.prec f g) π)
    {L : List Helper} (hL : ∀ y ∈ L, y ≠ .GEN ∧ y ≠ .CAT2 ∧ y ≠ .CAT2u ∧ y ≠ .GA ∧ y ≠ .GB ∧ y ≠ .TH ∧ y ≠ .D1 ∧
      y ≠ .D0 ∧ y ≠ .OUT ∧ y ≠ .GAEND ∧ y ≠ .GBEND)
    {x lp sep rp : Tok} {Nm : List Tok} {n : Nat} (hx : x.s = fullName π .GEN) (hxH : In π L x.H)
    (hlp : lp.s = "(") (hsep : sep.s = ",") (hrp : rp.s = ")") (hrpH : In π L rp.H) (hN : IsNum Nm n) (c : Nat) :
    ∃ M o st c', scan Γ M c (callToks x lp sep rp [Nm]) = some (o, st, c') ∧
      o.map (·.s) = (List.replicate n [fullName π .TH, "("]).flatten ∧ ∀ t ∈ o, t.s ∉ t.H := by
  let Ps : Nat → List Tok → Prop := fun j o => j = 0 → IsNum o n
  have hargs : ∀ j, ExpandsP Γ ([Nm].getD j []) (Ps j) := by
    intro j c0
    match j with
    | 0 =>
      have e := scan_nameFree' (nameFree_num hp hN) c0
      exact ⟨_, finalize Nm, [], c0, by simp only [List.getD, expand]; rw [show [Nm][0]?.getD [] = Nm from rfl, e]; rfl,
        fun _ => isNum_finalize' hN⟩
    | j + 1 => exact ⟨1, [], [], c0, by simp [expand, scan, finalize], fun h => absurd h (by omega)⟩
  have hf : Γ.find x.s = some (.fn 1 false [nm π .CAT2, tk "(", nm π .GA, prm 0, tk ",", tk "_END", tk ")"]) := by
    rw [hx]; exact find_prec hR .GEN
  have hplain : Plain [nm π .CAT2, tk "(", nm π .GA, prm 0, tk ",", tk "_END", tk ")"] := by
    intro b hb; simp [nm, tk, prm] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  obtain ⟨N, outs, c1, hos, hcall⟩ := call_plainP Γ hf (by rw [hx]; exact not_mem_of_in hxH (fun h => (hL _ h).1 rfl))
    hlp hsep hrp rfl (Or.inl (by decide)) (by intro A hA; simp at hA; subst hA; unfold ArgShape; exact walk_num hN 0)
    Ps hargs hplain c
  have hpi : paramIdx [nm π .CAT2, tk "(", nm π .GA, prm 0, tk ",", tk "_END", tk ")"] = [0] := by
    simp [nm, tk, prm, paramIdx]
  rw [hpi] at hos
  obtain ⟨o0, rfl, ho0, hfin0⟩ := all2_single hos
  let K := x.s :: inter x.H rp.H
  have hK : In π (.GEN :: L) K := by show In π (.GEN :: L) (x.s :: inter x.H rp.H); rw [hx]; exact in_mark hxH _ _
  have hbody : ∀ s, In π (.GEN :: L) (markOne c K { s }).H := fun s => in_markOne hK (in_nil _ _) c
  obtain ⟨M, o, st, c', e1, ho, hfin⟩ := cat2_stage Γ hp hR (L := .GEN :: L)
    (by
      intro y hy; simp at hy
      rcases hy with rfl | hy
      · decide
      · have h := hL y hy; exact h.2)
    (x := markOne c K { s := fullName π .CAT2 }) (lp := markOne c K { s := "(" }) (sep := markOne c K comma)
    (rp := markOne c K { s := ")" }) (ga := markOne c K { s := fullName π .GA }) (e := markOne c K { s := "_END" })
    (Nm := o0.map (markOne c K)) (n := n)
    rfl (hbody _) rfl rfl rfl (hbody _) rfl (hbody _) (isNum_markAll (ho0 rfl) c K)
    (by
      intro t ht; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
      exact inJ_marked hK (hfin0 t0 ht0) (num_not_name (ho0 rfl) t0 ht0) c)
    rfl (hbody _) c1
  have e1' := scanMono Γ M c1 _ _ e1 (max N M) (Nat.le_max_right _ _)
  obtain ⟨st', hfin'⟩ := hcall (max N M) (Nat.le_max_left _ _) (o, st, c') (by
    rw [toks_gen, mark_callToks]; exact e1')
  exact ⟨max N M + 1, o, st', c', hfin', ho, hfin⟩

end PP

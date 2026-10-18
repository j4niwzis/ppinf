/-
  Theorem 10, recursion, stage G: the `CAT` call and the `ITER` call.
-/
import CatStage

namespace PP

theorem walk_name {x : Tok} {π : List Code} {y : Helper} (hx : x.s = fullName π y) (d : Nat) (r : List Tok) :
    walk d (x :: r) = walk d r := by
  have h1 : (x.s == ")") = false := by rw [hx]; simpa using fullName_ne_rp π y
  have h2 : (x.s == "(") = false := by rw [hx]; simpa using fullName_ne_lp π y
  have h3 : (x.s == ",") = false := by rw [hx]; simpa using fullName_ne_comma π y
  simp [walk, h1, h2, h3]

/-- `GEN ( n̄ ) S BRA n̄` is an argument. -/
theorem argShape_a {π : List Code} {gen lp sep rp bra : Tok} {N1 S N2 : List Tok} {n c v : Nat} {ys : List Nat}
    (hg : gen.s = fullName π .GEN) (hlp : lp.s = "(") (hsep : sep.s = ",") (hrp : rp.s = ")") (hN1 : IsNum N1 n)
    (hS : IsTuple c v ys S) (hb : bra.s = fullName π .BRA) (hN2 : IsNum N2 n) :
    ArgShape (callToks gen lp sep rp [N1] ++ (S ++ bra :: N2)) := by
  have h1 := argShape_call (x := gen) (by rw [hg]; exact fullName_ne_rp _ _) (by rw [hg]; exact fullName_ne_lp _ _)
    (by rw [hg]; exact fullName_ne_comma _ _) hlp hsep hrp [N1] (by intro A hA; simp at hA; subst hA; exact ⟨n, hN1⟩)
  unfold ArgShape at *
  rw [walk_append, h1]; simp only [Option.bind_some]
  rw [walk_append, isTuple_shape hS]; simp only [Option.bind_some]
  rw [walk_name hb, walk_num hN2]

/-- The expansion of `GEN ( n̄ ) S BRA n̄`. -/
def AOut (π : List Code) (n v0 : Nat) (ys : List Nat) (E : List Tok) : Prop :=
  ∃ o1 S o2, E = o1 ++ (S ++ o2) ∧ o1.map (·.s) = (List.replicate n [fullName π .TH, "("]).flatten ∧
    (∀ t ∈ o1, t.H = []) ∧ IsTuple 0 v0 ys S ∧
    o2.map (·.s) = List.replicate n ")" ++ [if n % 2 = 0 then fullName π .BRA else fullName π .BRB] ∧ ∀ t ∈ o2, t.H = []

theorem finalize_append (a b : List Tok) : finalize (a ++ b) = finalize a ++ finalize b := by simp [finalize]

theorem finalize_spell (a : List Tok) : (finalize a).map (·.s) = a.map (·.s) := by simp [finalize, Function.comp_def]

theorem toks_cat (π : List Code) (E1 E2 : List Tok) :
    toks (plainOut [nm π .CATu, tk "(", prm 0, tk ",", prm 1, tk ")"] [E1, E2]) =
      callToks { s := fullName π .CATu } { s := "(" } comma { s := ")" } [E1, E2] := by
  simp only [nm, tk, prm, plainOut, toks_t]
  rw [toks_map_t, toks_t, toks_map_t, toks_t]
  simp [toks, callToks, joinArgs, comma]

/-- Inside an `ITER`: only the node's own macro, `SEL` and `ITER` are hidden among its helpers. -/
def Outer (L : List Helper) : Prop := ∀ y ∈ L, y = .self ∨ y = .SEL ∨ y = .ITER

theorem outer_not {L : List Helper} (h : Outer L) {X : Helper} (hX : X ≠ .self ∧ X ≠ .SEL ∧ X ≠ .ITER) : X ∉ L := by
  intro hm; rcases h X hm with e | e | e
  · exact hX.1 e
  · exact hX.2.1 e
  · exact hX.2.2 e

theorem expand_end {Γ : Env} (hp : PunctFree Γ) {π : List Code} {L : List Helper} {e : Tok} (he : e.s = "_END")
    (heH : In π L e.H) (c0 : Nat) : ∃ N, expand Γ N c0 [e] = some (finalize [e], [], c0) ∧
      (finalize [e]).map (·.s) = ["_END"] ∧ ∀ t ∈ finalize [e], t.H = [] := by
  have hfree : NameFree Γ [e] := by intro t ht; simp at ht; subst ht; rw [he]; exact hp.2.2.2.2
  have hn : e.s ∉ e.H := by rw [he]; exact name_ne_of_in heH (fun π' y => fullName_ne_end π' y)
  refine ⟨[e].length + 1, by unfold expand; rw [scan_nameFree' hfree c0]; rfl, by simp [finalize, he], ?_⟩
  intro t ht; simp [finalize] at ht; subst ht; simp [hn]

/-- **`CAT ( GEN ( n̄ ) S BRA n̄ , _END )`** → the recursion's tuple. -/
theorem cat_stage (Γ : Env) (hp : PunctFree Γ) {f g : Term} {π : List Code} (hR : Realizes Γ (.prec f g) π)
    (hga : g.arity = f.arity + 2) (IHg : NodeOK Γ g (π ++ [.r])) {L : List Helper} (hL : Outer L)
    {x lp sep rp gen lp2 sep2 rp2 bra e : Tok} {N1 S N2 : List Tok} {n v0 : Nat} {ys : List Nat}
    (hys : ys.length = f.arity)
    (hx : x.s = fullName π .CAT) (hxH : In π L x.H) (hlp : lp.s = "(") (hsep : sep.s = ",") (hrp : rp.s = ")")
    (hrpH : In π L rp.H) (hg : gen.s = fullName π .GEN) (hgH : In π L gen.H) (hlp2 : lp2.s = "(") (hsep2 : sep2.s = ",")
    (hrp2 : rp2.s = ")") (hrp2H : In π L rp2.H) (hN1 : IsNum N1 n) (hS : IsTuple 0 v0 ys S)
    (hb : bra.s = fullName π .BRA) (hbH : In π L bra.H) (hN2 : IsNum N2 n) (hN2H : ∀ t ∈ N2, InJ π L t.H)
    (he : e.s = "_END") (heH : In π L e.H) (c : Nat) :
    ∃ M o st c', scan Γ M c (callToks x lp sep rp [callToks gen lp2 sep2 rp2 [N1] ++ (S ++ bra :: N2), [e]]) =
      some (o, st, c') ∧ IsTuple n (recV g ys v0 n) ys o := by
  let Ps : Nat → List Tok → Prop := fun j E => if j = 0 then AOut π n v0 ys E else if j = 1 then
    (E.map (·.s) = ["_END"] ∧ ∀ t ∈ E, t.H = []) else True
  have hargs : ∀ j, ExpandsP Γ ([callToks gen lp2 sep2 rp2 [N1] ++ (S ++ bra :: N2), [e]].getD j []) (Ps j) := by
    intro j c0
    match j with
    | 0 =>
      obtain ⟨M, o1, o2, st, c', e1, ho1, ho2, hf1, hf2⟩ := a_stage Γ hp hR (L := L)
        (fun y hy => by rcases hL y hy with rfl | rfl | rfl <;> decide) hg hgH hlp2 hsep2 hrp2 hrp2H hN1
        (isTuple_nameFree hp hS) hb hbH hN2 hN2H c0
      refine ⟨M, finalize (o1 ++ (S ++ o2)), st, c', by simp [expand, e1], ?_⟩
      simp only [Ps, ite_true]
      refine ⟨finalize o1, finalize S, finalize o2, by simp [finalize_append], by rw [finalize_spell, ho1],
        finalize_H hf1, isTuple_map hS _ (fun t => rfl), by rw [finalize_spell, ho2], finalize_H hf2⟩
    | 1 =>
      obtain ⟨N, e1, h1, h2⟩ := expand_end hp he heH c0
      exact ⟨N, _, _, _, e1, by simp only [Ps]; exact ⟨h1, h2⟩⟩
    | j + 2 => exact ⟨1, [], [], c0, by simp [expand, scan, finalize], by simp [Ps]⟩
  have hs : ∀ A ∈ [callToks gen lp2 sep2 rp2 [N1] ++ (S ++ bra :: N2), [e]], ArgShape A := by
    intro A hA; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hA
    rcases hA with rfl | rfl
    · exact argShape_a hg hlp2 hsep2 hrp2 hN1 hS hb hN2
    · unfold ArgShape; rw [walk_spell]; simp [walkS, he]
  have hf : Γ.find x.s = some (.fn 2 false [nm π .CATu, tk "(", prm 0, tk ",", prm 1, tk ")"]) := by
    rw [hx]; exact find_prec hR .CAT
  have hplain : Plain [nm π .CATu, tk "(", prm 0, tk ",", prm 1, tk ")"] := by
    intro b hb; simp [nm, tk, prm] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  obtain ⟨N, outs, c1, hos, hcall⟩ := call_plainP Γ hf (by rw [hx]; exact not_mem_of_in hxH (outer_not hL (by decide)))
    hlp hsep hrp rfl (Or.inl (by decide)) hs Ps hargs hplain c
  have hpi : paramIdx [nm π .CATu, tk "(", prm 0, tk ",", prm 1, tk ")"] = [0, 1] := by simp [nm, tk, prm, paramIdx]
  rw [hpi] at hos
  obtain ⟨Ea, E2, rfl, ⟨hP1, _⟩, ⟨hP2, _⟩⟩ : ∃ E1 E2, outs = [E1, E2] ∧ (Ps 0 E1 ∧ Fin E1) ∧ (Ps 1 E2 ∧ Fin E2) := by
    cases hos with
    | cons h1 hr => cases hr with
      | cons h2 hr' => cases hr'; exact ⟨_, _, rfl, h1, h2⟩
  simp only [Ps, ite_true, Nat.one_ne_zero, ite_false] at hP1 hP2
  obtain ⟨e2, rfl, he2⟩ : ∃ e2, E2 = [e2] ∧ e2.s = "_END" := by
    match E2, hP2.1 with
    | [e2], h => exact ⟨e2, rfl, by simpa using h⟩
    | [], h => simp at h
    | _ :: _ :: _, h => simp at h
  obtain ⟨o1, S1, o2, rfl, ho1, hh1, hS1, ho2, hh2⟩ := hP1
  let K := x.s :: inter x.H rp.H
  have hK : In π (.CAT :: L) K := by show In π (.CAT :: L) (x.s :: inter x.H rp.H); rw [hx]; exact in_mark hxH _ _
  let mk := markOne c K
  have hin : ∀ t : Tok, t.H = [] → In π (.CAT :: L) (mk t).H := fun t ht => in_markOne hK (in_of_nil ht) c
  obtain ⟨P, hPe, hPl, hPs⟩ := pair_split _ _ n (o1.map mk) (by simpa [Function.comp_def, mk, markOne_s] using ho1)
  obtain ⟨R, Z, hRe, hRl, hRs, hZs⟩ := rp_split _ n (o2.map mk) (by simpa [Function.comp_def, mk, markOne_s] using ho2)
  have memo1 : ∀ t ∈ o1.map mk, In π (.CAT :: L) t.H := by
    intro t ht; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht; exact hin t0 (hh1 t0 ht0)
  have memo2 : ∀ t ∈ o2.map mk, In π (.CAT :: L) t.H := by
    intro t ht; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht; exact hin t0 (hh2 t0 ht0)
  obtain ⟨M, o, st, c', e1, ho⟩ := catu_stage Γ hp hR hga IHg (L := .CAT :: L)
    (by
      intro y hy; simp at hy
      rcases hy with rfl | hy
      · decide
      · rcases hL y hy with rfl | rfl | rfl <;> decide)
    (x := mk { s := fullName π .CATu }) (lp := mk { s := "(" }) (sep := mk comma) (rp := mk { s := ")" })
    (e := mk e2) (P := P) (S := S1.map mk) (R := R) (Z := Z)
    rfl (hin _ rfl) rfl rfl rfl (hin _ rfl)
    (by
      intro p hp'
      obtain ⟨h1, h2⟩ := hPs p hp'
      exact ⟨h1, h2, memo1 p.1 (by rw [hPe]; exact List.mem_flatMap.mpr ⟨p, hp', by simp⟩)⟩)
    hPl (isTuple_map hS1 mk (fun t => rfl)) hys hRs hRl hZs (memo2 Z (by rw [hRe]; simp))
    he2 (hin e2 (hP2.2 e2 (by simp))) c1
  have e1' := scanMono Γ M c1 _ _ e1 (max N M) (Nat.le_max_right _ _)
  obtain ⟨st', hfin'⟩ := hcall (max N M) (Nat.le_max_left _ _) (o, st, c') (by
    rw [toks_cat, mark_callToks]
    have : mark c K (o1 ++ (S1 ++ o2)) = P.flatMap (fun p => [p.1, p.2]) ++ S1.map mk ++ R ++ [Z] := by
      rw [mark_eq, List.map_append, List.map_append, ← hPe, ← List.append_assoc, hRe]; simp [mk]
    simp only [List.map_cons, List.map_nil]
    rw [this]; exact e1')
  exact ⟨max N M + 1, o, st', c', hfin', ho⟩

def iterBody (π : List Code) : List BTok :=
  [nm π .CAT, tk "(", nm π .GEN, tk "(", prm 0, tk ")", prm 1, nm π .BRA, prm 0, tk ",", tk "_END", tk ")"]

theorem toks_iter (π : List Code) (o1 oS o2 : List Tok) :
    toks (plainOut (iterBody π) [o1, oS, o2]) =
      callToks { s := fullName π .CAT } { s := "(" } comma { s := ")" }
        [callToks { s := fullName π .GEN } { s := "(" } comma { s := ")" } [o1] ++ (oS ++ { s := fullName π .BRA } :: o2),
         [{ s := "_END" }]] := by
  simp only [iterBody, nm, tk, prm, plainOut, toks_t]
  rw [toks_map_t, toks_t, toks_map_t, toks_t, toks_map_t]
  simp [toks, tokOf, callToks, joinArgs, comma]

/-- **`ITER ( n̄ , B )`**, `B` expanding to the base tuple. -/
theorem iter_stage (Γ : Env) (hp : PunctFree Γ) {f g : Term} {π : List Code} (hR : Realizes Γ (.prec f g) π)
    (hga : g.arity = f.arity + 2) (IHg : NodeOK Γ g (π ++ [.r])) {L : List Helper}
    (hL : ∀ y ∈ L, y = .self ∨ y = .SEL) {x lp sep rp : Tok} {A B : List Tok} {n v0 : Nat} {ys : List Nat} (hys : ys.length = f.arity)
    (hx : x.s = fullName π .ITER) (hxH : In π L x.H) (hlp : lp.s = "(") (hsep : sep.s = ",") (hrp : rp.s = ")")
    (hrpH : In π L rp.H) (hA : ArgShape A) (hAe : ExpandsP Γ A (fun o => IsNum o n)) (hB : ArgShape B)
    (hBe : ExpandsP Γ B (IsTuple 0 v0 ys)) (c : Nat) :
    ∃ M o st c', scan Γ M c (callToks x lp sep rp [A, B]) = some (o, st, c') ∧ IsTuple n (recV g ys v0 n) ys o := by
  have hLI : Outer (.ITER :: L) := by
    intro y hy; simp at hy; rcases hy with rfl | hy
    · exact Or.inr (Or.inr rfl)
    · rcases hL y hy with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  let Ps : Nat → List Tok → Prop := fun j E => if j = 0 then IsNum E n else if j = 1 then IsTuple 0 v0 ys E else True
  have hargs : ∀ j, ExpandsP Γ ([A, B].getD j []) (Ps j) := by
    intro j c0
    match j with
    | 0 => obtain ⟨N, o, st, c', e, ho⟩ := hAe c0; exact ⟨N, o, st, c', e, by simpa [Ps] using ho⟩
    | 1 => obtain ⟨N, o, st, c', e, ho⟩ := hBe c0; exact ⟨N, o, st, c', e, by simpa [Ps] using ho⟩
    | j + 2 => exact ⟨1, [], [], c0, by simp [expand, scan, finalize], by simp [Ps]⟩
  have hf : Γ.find x.s = some (.fn 2 false (iterBody π)) := by rw [hx]; exact find_prec hR .ITER
  have hplain : Plain (iterBody π) := by
    intro b hb; simp [iterBody, nm, tk, prm] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have nITER : Helper.ITER ∉ L := by intro h; rcases hL _ h with e | e <;> cases e
  obtain ⟨N, outs, c1, hos, hcall⟩ := call_plainP Γ hf (by rw [hx]; exact not_mem_of_in hxH nITER)
    hlp hsep hrp rfl (Or.inl (by decide)) (by intro X hX; simp at hX; rcases hX with rfl | rfl <;> assumption)
    Ps hargs hplain c
  have hpi : paramIdx (iterBody π) = [0, 1, 0] := by simp [iterBody, nm, tk, prm, paramIdx]
  rw [hpi] at hos
  obtain ⟨o1, oS, o2, rfl, ⟨h1, f1⟩, ⟨hS, _⟩, ⟨h2, f2⟩⟩ : ∃ a b d, outs = [a, b, d] ∧ (Ps 0 a ∧ Fin a) ∧
      (Ps 1 b ∧ Fin b) ∧ (Ps 0 d ∧ Fin d) := by
    cases hos with
    | cons ha r1 => cases r1 with
      | cons hb r2 => cases r2 with
        | cons hd r3 => cases r3; exact ⟨_, _, _, rfl, ha, hb, hd⟩
  simp only [Ps, ite_true, Nat.one_ne_zero, ite_false] at h1 hS h2
  let K := x.s :: inter x.H rp.H
  have hK : In π (.ITER :: L) K := by show In π (.ITER :: L) (x.s :: inter x.H rp.H); rw [hx]; exact in_mark hxH _ _
  let mk := markOne c K
  have hin : ∀ t : Tok, t.H = [] → In π (.ITER :: L) (mk t).H := fun t ht => in_markOne hK (in_of_nil ht) c
  obtain ⟨M, o, st, c', e1, ho⟩ := cat_stage Γ hp hR hga IHg hLI (x := mk { s := fullName π .CAT })
    (lp := mk { s := "(" }) (sep := mk comma) (rp := mk { s := ")" }) (gen := mk { s := fullName π .GEN })
    (lp2 := mk { s := "(" }) (sep2 := mk comma) (rp2 := mk { s := ")" }) (bra := mk { s := fullName π .BRA })
    (e := mk { s := "_END" }) (N1 := o1.map mk) (S := oS.map mk) (N2 := o2.map mk) hys
    rfl (hin _ rfl) rfl rfl rfl (hin _ rfl) rfl (hin _ rfl) rfl rfl rfl (hin _ rfl) (isNum_markAll h1 c K)
    (isTuple_map hS mk (fun t => rfl)) rfl (hin _ rfl) (isNum_markAll h2 c K)
    (by
      intro t ht; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
      exact inJ_marked hK (f2 t0 ht0) (num_not_name h2 t0 ht0) c)
    rfl (hin _ rfl) c1
  have e1' := scanMono Γ M c1 _ _ e1 (max N M) (Nat.le_max_right _ _)
  obtain ⟨st', hfin'⟩ := hcall (max N M) (Nat.le_max_left _ _) (o, st, c') (by
    have hl : mark c K (toks (plainOut (iterBody π) [o1, oS, o2])) =
        callToks (mk { s := fullName π .CAT }) (mk { s := "(" }) (mk comma) (mk { s := ")" })
          [callToks (mk { s := fullName π .GEN }) (mk { s := "(" }) (mk comma) (mk { s := ")" }) [o1.map mk] ++
            (oS.map mk ++ mk { s := fullName π .BRA } :: o2.map mk), [mk { s := "_END" }]] := by
      rw [toks_iter, mark_eq]; simp [callToks, joinArgs, mk]
    rw [hl]; exact e1')
  exact ⟨max N M + 1, o, st', c', hfin', ho⟩

end PP

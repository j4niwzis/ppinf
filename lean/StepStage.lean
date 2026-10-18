/-
  Theorem 10, recursion, stage F: `STEP ( c̄ , v̄ , ȳ )` → `( c+1 , g(c, v, ȳ) , ȳ )`.
-/
import StepShape

namespace PP

theorem all2_range_off {P : List Tok → Nat → Prop} {m : Nat} {Y : List (List Tok)} {a b : Nat} {ys : List Nat}
    (hys : ys.length = m) (h : All2 (fun j o => P o ((a :: b :: ys).getD j 0)) ((List.range m).map (2 + ·)) Y) :
    All2 P Y ys := by
  obtain ⟨hl, hi⟩ := all2_iff.mp h
  refine all2_iff.mpr ⟨by simp at hl; omega, fun i h1 h2 => ?_⟩
  have := hi i (by simp; omega) h1
  simp only [List.getElem_map, List.getElem_range] at this
  rwa [show 2 + i = i + 2 by omega, List.getD_cons_succ, List.getD_cons_succ, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h2, Option.getD_some] at this

theorem expandsP_of_argsOK {Γ : Env} {as : List (List Tok)} {vs : List Nat} (h : ArgsOK Γ as vs) (j : Nat) :
    ExpandsP Γ (as.getD j []) (fun o => IsNum o (vs.getD j 0)) := fun c => expands_getD h j c

theorem lastOK_num {Γ : Env} (hp : PunctFree Γ) {o : List Tok} {v : Nat} (h : IsNum o v) : LastOK Γ o := by
  intro x hx; right; intro a w b e
  have hm : x ∈ o := List.mem_of_getLast? hx
  rw [nameFree_num hp h x hm] at e; cases e

theorem plain_tailB (ps : List Nat) : Plain (tailB (ps.map prm)) := by
  intro b hb
  simp only [tailB, List.mem_flatMap, List.mem_map] at hb
  obtain ⟨_, ⟨p, _, rfl⟩, hb⟩ := hb
  simp [tk, prm] at hb; rcases hb with rfl | rfl <;> simp

theorem plain_stepBody (π : List Code) (m : Nat) : Plain (stepBody π m) := by
  unfold stepBody; rw [prms_eq]
  refine plain_append (plain_append (plain_append (plain_append ?_ (plain_tailB _)) (plain_single _ (by simp [tk])))
    (plain_tailB _)) (plain_single _ (by simp [tk]))
  intro b hb; simp [tk, prm, nm] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem map_flatMap_cons (f : Tok → Tok) (sep : Tok) (Y : List (List Tok)) :
    (Y.flatMap fun o => sep :: o).map f = (Y.map (List.map f)).flatMap fun o => f sep :: o := by
  induction Y with
  | nil => rfl
  | cons y Y ih => simp [ih]

theorem nameFree_append {Γ : Env} {a b : List Tok} (ha : NameFree Γ a) (hb : NameFree Γ b) : NameFree Γ (a ++ b) := by
  intro t ht; rcases List.mem_append.mp ht with h | h
  · exact ha t h
  · exact hb t h

theorem nameFree_nums {Γ : Env} (hp : PunctFree Γ) {Y : List (List Tok)} {ys : List Nat}
    (h : All2 (fun o v => IsNum o v) Y ys) : ∀ o ∈ Y, NameFree Γ o := by
  intro o ho
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ho
  obtain ⟨hl, hh⟩ := all2_iff.mp h
  exact nameFree_num hp (hh i hi (by omega))

theorem nameFree_flat {Γ : Env} (hp : PunctFree Γ) {sep : Tok} (hsep : sep.s = ",") {Y : List (List Tok)}
    (h : ∀ o ∈ Y, NameFree Γ o) : NameFree Γ (Y.flatMap fun o => sep :: o) := by
  intro t ht
  obtain ⟨o, ho, ht⟩ := List.mem_flatMap.mp ht
  rcases List.mem_cons.mp ht with rfl | ht
  · rw [hsep]; exact hp.2.2.1
  · exact h o ho t ht

/-- **`STEP ( c̄ , v̄ , ȳ )` → `( c+1 , g(c, v, ȳ) , ȳ )`.** -/
theorem step_stage (Γ : Env) (hp : PunctFree Γ) {f g : Term} {π : List Code} (hR : Realizes Γ (.prec f g) π)
    (hga : g.arity = f.arity + 2) (IHg : NodeOK Γ g (π ++ [.r])) {L : List Helper} (hL : Helper.STEP ∉ L)
    {x lp sep rp : Tok} {C V : List Tok} {Ys : List (List Tok)} {c v : Nat} {ys : List Nat}
    (hx : x.s = fullName π .STEP) (hxH : In π L x.H) (hlp : lp.s = "(") (hsep : sep.s = ",") (hrp : rp.s = ")")
    (hC : IsNum C c) (hV : IsNum V v) (hYs : All2 (fun Y y => IsNum Y y) Ys ys) (hys : ys.length = f.arity) (c0 : Nat) :
    ∃ M o st c', scan Γ M c0 (x :: tupToks lp sep rp C V Ys) = some (o, st, c') ∧
      IsTuple (c + 1) (g.eval (c :: v :: ys)) ys o := by
  let m := f.arity
  have hargs : ArgsOK Γ (C :: V :: Ys) (c :: v :: ys) := argsOK_nums hp (.cons hC (.cons hV hYs))
  have hYl : Ys.length = m := by have := all2_length hYs; show Ys.length = f.arity; omega
  have hf : Γ.find x.s = some (.fn (m + 2) false (stepBody π m)) := by rw [hx]; exact find_prec hR .STEP
  obtain ⟨N, outs, c1, hos, hcall⟩ := call_plainP Γ hf (by rw [hx]; exact not_mem_of_in hxH hL) hlp hsep hrp
    (by simp [hYl]) (Or.inl (by omega)) (argShape_of_ok hargs) _ (expandsP_of_argsOK hargs) (plain_stepBody π m) c0
  rw [paramIdx_step, List.append_assoc] at hos
  obtain ⟨o3, oY, rfl, h3, hY⟩ := all2_append hos
  obtain ⟨Y1, Y2, rfl, hY1, hY2⟩ := all2_append hY
  obtain ⟨oc1, oc2, ov, rfl, hc1, hc2, hv⟩ : ∃ a b d, o3 = [a, b, d] ∧ (IsNum a c ∧ Fin a) ∧ (IsNum b c ∧ Fin b) ∧
      (IsNum d v ∧ Fin d) := by
    cases h3 with
    | cons ha r1 => cases r1 with
      | cons hb r2 => cases r2 with
        | cons hd r3 => cases r3; exact ⟨_, _, _, rfl, ha, hb, hd⟩
  have hY1' := all2_range_off hys (P := fun o y => IsNum o y ∧ Fin o) hY1
  have hY2' := all2_range_off hys (P := fun o y => IsNum o y ∧ Fin o) hY2
  have hY1l : Y1.length = m := by have := all2_length hY1'; show Y1.length = f.arity; omega
  have hY2l : Y2.length = m := by have := all2_length hY2'; show Y2.length = f.arity; omega
  -- the marked replacement
  let K := x.s :: inter x.H rp.H
  have hK : In π (.STEP :: L) K := by show In π (.STEP :: L) (x.s :: inter x.H rp.H); rw [hx]; exact in_mark hxH _ _
  let mk := markOne c0 K
  have nums : ∀ {o : List Tok} {w : Nat}, IsNum o w → IsNum (o.map mk) w := fun h => isNum_markAll h c0 K
  -- `g ( c̄ , v̄ , ȳ )` by its node lemma
  have hY1n : All2 (fun Y y => IsNum Y y) (Y1.map (List.map mk)) ys :=
    all2_map_fst (R := fun o y => IsNum o y ∧ Fin o) (fun o y h => nums h.1) hY1'
  obtain ⟨N2, W, st2, c2, eg, hW⟩ := IHg (mk { s := fullName (π ++ [.r]) .self }) (mk { s := "(" }) (mk comma)
    (mk { s := ")" }) ((oc2 :: ov :: Y1).map (List.map mk)) (c :: v :: ys) rfl
    (fun hm => child_not_in hK .r (mem_markOne_body.mp hm)) rfl rfl rfl (by simp [hY1l, hga, m])
    (argsOK_nums hp (.cons (nums hc2.1) (.cons (nums hv.1) hY1n)))
    (fun n hn => in_child hK .r n (mem_markOne_body.mp (mem_inter.mp hn).1)) c1
  -- the rest `, ȳ )`, emitted
  let rest := (Y2.map (List.map mk)).flatMap (fun o => mk comma :: o) ++ [mk { s := ")" }]
  have hrest : NameFree Γ rest := nameFree_append
    (nameFree_flat hp rfl (nameFree_nums hp (all2_map_fst (R := fun o y => IsNum o y ∧ Fin o) (fun o y h => nums h.1) hY2')))
    (by intro t ht; simp at ht; subst ht; exact hp.2.1)
  have e1 := scan_frame2 Γ _ rest N2 c1 (W, st2, c2) eg (lastOK_num hp hW) _ _ (scan_nameFree' hrest c2)
  -- the front `( c̄ ( ~ ) ,`, emitted
  let front := mk { s := "(" } :: (oc1.map mk ++ [mk { s := "(" }, mk { s := "~" }, mk { s := ")" }, mk comma])
  have hfront : NameFree Γ front := by
    intro t ht
    simp only [front, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | ht | rfl | rfl | rfl | rfl
    · exact hp.1
    · exact nameFree_num hp (nums hc1.1) t ht
    · exact hp.1
    · exact hp.2.2.2.1
    · exact hp.2.1
    · exact hp.2.2.1
  have e2 := scan_nameFree_prefix Γ front hfront e1
  let n0 := max N (N2 + (rest.length + 1) + front.length)
  have e2' := scanMono Γ _ c1 _ _ e2 n0 (Nat.le_max_right _ _)
  have e3 : scan Γ n0 c1 (mark c0 K (toks (plainOut (stepBody π m) ([oc1, oc2, ov] ++ (Y1 ++ Y2))))) =
      some (front ++ (W ++ rest), st2 ++ [], c2) := by
    have hl : mark c0 K (toks (plainOut (stepBody π m) ([oc1, oc2, ov] ++ (Y1 ++ Y2)))) =
        front ++ (callToks (mk { s := fullName (π ++ [.r]) .self }) (mk { s := "(" }) (mk comma) (mk { s := ")" })
          ((oc2 :: ov :: Y1).map (List.map mk)) ++ rest) := by
      rw [← List.append_assoc, toks_step π m oc1 oc2 ov Y1 Y2 hY1l hY2l, mark_eq]
      simp [front, rest, callToks, map_joinArgs, map_flatMap_cons, mk]
    rw [hl]; exact e2'
  obtain ⟨st', efin⟩ := hcall n0 (Nat.le_max_left _ _) _ e3
  refine ⟨_, _, st', _, by simpa [callToks, tupToks] using efin, ?_⟩
  refine ⟨mk { s := "(" }, mk comma, mk { s := ")" }, oc1.map mk ++ [mk { s := "(" }, mk { s := "~" }, mk { s := ")" }], W,
    Y2.map (List.map mk), ?_, rfl, rfl, rfl, ?_, hW, ?_⟩
  · simp [tupToks, joinArgs_cons_flat, front, rest, List.append_assoc]
  · unfold IsNum; rw [unaryList_succ']; simp [mk, markOne_s]
    exact hc1.1
  · exact all2_map_fst (R := fun o y => IsNum o y ∧ Fin o) (fun o y h => nums h.1) hY2'

end PP

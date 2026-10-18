/-
  Theorem 10, recursion, stage H: `SEL2 ( c̄ , v̄ , … )` → `v̄`, and `SEL ( T )` with `T` expanding
  to a tuple.
-/
import IterStage

namespace PP

/-- **`SEL2`**, variadic: the second component. -/
theorem sel2_stage (Γ : Env) (hp : PunctFree Γ) {f g : Term} {π : List Code} (hR : Realizes Γ (.prec f g) π)
    {x lp sep rp : Tok} {C V : List Tok} {Ys : List (List Tok)} {c v : Nat} {ys : List Nat}
    (hx : x.s = fullName π .SEL2) (hid : x.s ∉ x.H) (hlp : lp.s = "(") (hsep : sep.s = ",") (hrp : rp.s = ")")
    (hC : IsNum C c) (hV : IsNum V v) (hYs : All2 (fun Y y => IsNum Y y) Ys ys) (c0 : Nat) :
    ∃ M o st c', scan Γ M c0 (x :: tupToks lp sep rp C V Ys) = some (o, st, c') ∧ IsNum o v := by
  have hs : ∀ X ∈ C :: V :: Ys, ArgShape X := argShape_of_ok (argsOK_nums hp (.cons hC (.cons hV hYs)))
  have hc := closeAt_args sep rp hsep hrp (C :: V :: Ys) [] [] hs
  simp only [List.reverse_nil, List.nil_append] at hc
  have hb : ∃ va, bind 2 true (joinArgs sep (C :: V :: Ys)) = some ([C, V], va) := by
    unfold bind
    rw [splitTop_args sep hsep C (V :: Ys) [] hs]
    simp
  obtain ⟨va, hb⟩ := hb
  have hf : Γ.find x.s = some (.fn 2 true [prm 1]) := by rw [hx]; exact find_prec hR .SEL2
  let N := V.length + 1
  have eV : expand Γ N (c0 + 1) V = some (finalize V, [], c0 + 1) := by
    unfold expand; rw [scan_nameFree' (nameFree_num hp hV) (c0 + 1)]; rfl
  have hr : subst Γ N (c0 + 1) [prm 1] [C, V] va = some ((finalize V).map RTok.t, [], c0 + 1) := by
    simp [subst, substFrom, piece, one, adjacentPaste, prm, eV]
  have hpaste := paste_noop _ (noOp_map_t (finalize V))
  rw [toks_map] at hpaste
  let R := mark c0 (x.s :: inter x.H rp.H) (finalize V)
  have hRn : IsNum R v := isNum_mark (isNum_finalize' hV) _ _
  obtain ⟨n, hn, e⟩ := rescan_num hp hRn (c0 + 1) N
  have hr' := subst_mono Γ hr n hn
  have := scan_fn_step Γ n c0 x lp rp (joinArgs sep (C :: V :: Ys)) [] hid hf hlp hc _ _ _ _ _ hb hr' hpaste
    (by simpa using e)
  exact ⟨n + 1, R, _, _, by simpa [tupToks] using this, hRn⟩

theorem toks_sel (π : List Code) (o : List Tok) :
    toks (plainOut [nm π .SEL2, prm 0] [o]) = { s := fullName π .SEL2 } :: o := by
  simp only [nm, tk, prm, plainOut, toks_t]; rw [toks_map_t]; simp [toks]

/-- **`SEL ( T )`**, `T` expanding to a tuple: its second component. -/
theorem sel_stage (Γ : Env) (hp : PunctFree Γ) {f g : Term} {π : List Code} (hR : Realizes Γ (.prec f g) π)
    {L : List Helper} (hSEL : Helper.SEL ∉ L) (hSEL2 : Helper.SEL2 ∉ L) {x lp sep rp : Tok} {T : List Tok}
    {c v : Nat} {ys : List Nat} (hx : x.s = fullName π .SEL) (hxH : In π L x.H) (hlp : lp.s = "(") (hsep : sep.s = ",")
    (hrp : rp.s = ")") (hT : ArgShape T) (hTe : ExpandsP Γ T (IsTuple c v ys)) (c0 : Nat) :
    ∃ M o st c', scan Γ M c0 (callToks x lp sep rp [T]) = some (o, st, c') ∧ IsNum o v := by
  let Ps : Nat → List Tok → Prop := fun j o => j = 0 → IsTuple c v ys o
  have hargs : ∀ j, ExpandsP Γ ([T].getD j []) (Ps j) := by
    intro j c1
    match j with
    | 0 => obtain ⟨N, o, st, c', e, ho⟩ := hTe c1; exact ⟨N, o, st, c', e, fun _ => ho⟩
    | j + 1 => exact ⟨1, [], [], c1, by simp [expand, scan, finalize], fun h => absurd h (by omega)⟩
  have hf : Γ.find x.s = some (.fn 1 false [nm π .SEL2, prm 0]) := by rw [hx]; exact find_prec hR .SEL
  obtain ⟨N, outs, c1, hos, hcall⟩ := call_plainP Γ hf (by rw [hx]; exact not_mem_of_in hxH hSEL) hlp hsep hrp rfl
    (Or.inl (by decide)) (by intro A hA; simp at hA; subst hA; exact hT) Ps hargs
    (by intro b hb; simp [nm, tk, prm] at hb; rcases hb with rfl | rfl <;> simp) c0
  have hpi : paramIdx [nm π .SEL2, prm 0] = [0] := by simp [nm, tk, prm, paramIdx]
  rw [hpi] at hos
  obtain ⟨o, rfl, ho, _⟩ := all2_single hos
  obtain ⟨lp', sep', rp', C, V, Ys, rfl, hlp', hsep', hrp', hC, hV, hYs⟩ := ho rfl
  let K := x.s :: inter x.H rp.H
  have hK : In π (.SEL :: L) K := by show In π (.SEL :: L) (x.s :: inter x.H rp.H); rw [hx]; exact in_mark hxH _ _
  let mk := markOne c0 K
  have num : ∀ {o : List Tok} {w : Nat}, IsNum o w → IsNum (o.map mk) w := fun h => isNum_markAll h c0 K
  obtain ⟨M, o', st, c', e1, ho'⟩ := sel2_stage Γ hp hR (x := mk { s := fullName π .SEL2 }) (lp := mk lp') (sep := mk sep')
    (rp := mk rp') (C := C.map mk) (V := V.map mk) (Ys := Ys.map (List.map mk)) rfl
    (not_mem_of_in (in_markOne hK (in_nil _ _) c0) (by simp [hSEL2])) hlp' hsep' hrp' (num hC) (num hV)
    (all2_map_fst (fun o y h => num h) hYs) c1
  have e1' := scanMono Γ M c1 _ _ e1 (max N M) (Nat.le_max_right _ _)
  obtain ⟨st', efin⟩ := hcall (max N M) (Nat.le_max_left _ _) _ (by
    rw [toks_sel, mark_eq, List.map_cons, map_tupToks]; exact e1')
  exact ⟨_, o', st', c', efin, ho'⟩

end PP

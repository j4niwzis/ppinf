/-
  Theorem 10, recursion, stage F: `TH ( T )` with `T` expanding to `( c̄ , v̄ , ȳ )` scans to
  `( c+1 , g(c, v, ȳ) , ȳ )`; and `n` nested `TH`s, from the base tuple, to the recursion's value.
-/
import StepStage

namespace PP

theorem map_tupToks (f : Tok → Tok) (lp sep rp : Tok) (C V : List Tok) (Ys : List (List Tok)) :
    (tupToks lp sep rp C V Ys).map f = tupToks (f lp) (f sep) (f rp) (C.map f) (V.map f) (Ys.map (List.map f)) := by
  simp [tupToks, map_joinArgs]

theorem isTuple_map {c v : Nat} {ys : List Nat} {E : List Tok} (h : IsTuple c v ys E) (f : Tok → Tok)
    (hf : ∀ t, (f t).s = t.s) : IsTuple c v ys (E.map f) := by
  obtain ⟨lp, sep, rp, C, V, Ys, rfl, hlp, hsep, hrp, hC, hV, hYs⟩ := h
  have num : ∀ {o : List Tok} {w : Nat}, IsNum o w → IsNum (o.map f) w := by
    intro o w h; unfold IsNum at *; simp [Function.comp_def, hf, h]
  exact ⟨_, _, _, _, _, _, map_tupToks f lp sep rp C V Ys, by rw [hf, hlp], by rw [hf, hsep], by rw [hf, hrp],
    num hC, num hV, all2_map_fst (fun o y h => num h) hYs⟩

theorem isTuple_nameFree {Γ : Env} (hp : PunctFree Γ) {c v : Nat} {ys : List Nat} {E : List Tok} (h : IsTuple c v ys E) :
    NameFree Γ E := by
  obtain ⟨lp, sep, rp, C, V, Ys, rfl, hlp, hsep, hrp, hC, hV, hYs⟩ := h
  intro t ht
  simp only [tupToks, List.mem_append, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at ht
  rcases ht with (rfl | ht) | rfl
  · rw [hlp]; exact hp.1
  · rw [joinArgs_cons_flat] at ht
    rcases List.mem_append.mp ht with ht | ht
    · exact nameFree_num hp hC t ht
    · exact nameFree_flat hp hsep (by
        intro o ho; rcases List.mem_cons.mp ho with rfl | ho
        · exact nameFree_num hp hV
        · exact nameFree_nums hp hYs o ho) t (by simpa using ht)
  · rw [hrp]; exact hp.2.1

theorem isTuple_shape {c v : Nat} {ys : List Nat} {E : List Tok} (h : IsTuple c v ys E) : ArgShape E := by
  obtain ⟨lp, sep, rp, C, V, Ys, rfl, hlp, hsep, hrp, hC, hV, hYs⟩ := h
  refine argShape_tuple hlp hsep hrp (fun A hA => ?_)
  rcases List.mem_cons.mp hA with rfl | hA
  · exact ⟨c, hC⟩
  rcases List.mem_cons.mp hA with rfl | hA
  · exact ⟨v, hV⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hA
  obtain ⟨hl, hh⟩ := all2_iff.mp hYs
  exact ⟨_, hh i hi (by omega)⟩

/-- A tuple is expanded to itself. -/
theorem expands_tuple {Γ : Env} (hp : PunctFree Γ) {c v : Nat} {ys : List Nat} {E : List Tok} (h : IsTuple c v ys E) :
    ExpandsP Γ E (IsTuple c v ys) := fun c0 =>
  ⟨E.length + 1, finalize E, [], c0, by simp only [expand, scan_nameFree' (isTuple_nameFree hp h) c0, Option.map_some],
    isTuple_map h _ (fun t => rfl)⟩

theorem toks_th (π : List Code) (o : List Tok) :
    toks (plainOut [nm π .STEP, prm 0] [o]) = { s := fullName π .STEP } :: o := by
  simp only [nm, tk, prm, plainOut, toks_t]; rw [toks_map_t]; simp [toks]

/-- **One level: `TH ( T )`.** -/
theorem th_level (Γ : Env) (hp : PunctFree Γ) {f g : Term} {π : List Code} (hR : Realizes Γ (.prec f g) π)
    (hga : g.arity = f.arity + 2) (IHg : NodeOK Γ g (π ++ [.r])) {L : List Helper} (hTH : Helper.TH ∉ L)
    (hSTEP : Helper.STEP ∉ L) {th lp sep rp : Tok} {T : List Tok} {c v : Nat} {ys : List Nat} (hys : ys.length = f.arity)
    (hth : th.s = fullName π .TH) (hthH : In π L th.H) (hlp : lp.s = "(") (hsep : sep.s = ",") (hrp : rp.s = ")")
    (hT : ArgShape T) (hTe : ExpandsP Γ T (IsTuple c v ys)) (c0 : Nat) :
    ∃ M o st c', scan Γ M c0 (callToks th lp sep rp [T]) = some (o, st, c') ∧
      IsTuple (c + 1) (g.eval (c :: v :: ys)) ys o := by
  let Ps : Nat → List Tok → Prop := fun j o => j = 0 → IsTuple c v ys o
  have hargs : ∀ j, ExpandsP Γ ([T].getD j []) (Ps j) := by
    intro j c1
    match j with
    | 0 => obtain ⟨N, o, st, c', e, ho⟩ := hTe c1; exact ⟨N, o, st, c', e, fun _ => ho⟩
    | j + 1 => exact ⟨1, [], [], c1, by simp [expand, scan, finalize], fun h => absurd h (by omega)⟩
  have hf : Γ.find th.s = some (.fn 1 false [nm π .STEP, prm 0]) := by rw [hth]; exact find_prec hR .TH
  obtain ⟨N, outs, c1, hos, hcall⟩ := call_plainP Γ hf (by rw [hth]; exact not_mem_of_in hthH hTH) hlp hsep hrp rfl
    (Or.inl (by decide)) (by intro A hA; simp at hA; subst hA; exact hT) Ps hargs
    (by intro b hb; simp [nm, tk, prm] at hb; rcases hb with rfl | rfl <;> simp) c0
  have hpi : paramIdx [nm π .STEP, prm 0] = [0] := by simp [nm, tk, prm, paramIdx]
  rw [hpi] at hos
  obtain ⟨o, rfl, ho, _⟩ := all2_single hos
  obtain ⟨lp', sep', rp', C, V, Ys, rfl, hlp', hsep', hrp', hC, hV, hYs⟩ := ho rfl
  let K := th.s :: inter th.H rp.H
  have hK : In π (.TH :: L) K := by show In π (.TH :: L) (th.s :: inter th.H rp.H); rw [hth]; exact in_mark hthH _ _
  let mk := markOne c0 K
  have num : ∀ {o : List Tok} {w : Nat}, IsNum o w → IsNum (o.map mk) w := fun h => isNum_markAll h c0 K
  have hys' : ys.length = f.arity := hys
  obtain ⟨M, o', st, c', e1, ho'⟩ := step_stage Γ hp hR hga IHg (L := .TH :: L) (by simp [hSTEP])
    (x := mk { s := fullName π .STEP }) (lp := mk lp') (sep := mk sep') (rp := mk rp') (C := C.map mk) (V := V.map mk)
    (Ys := Ys.map (List.map mk)) rfl (in_markOne hK (in_nil _ _) c0) hlp' hsep' hrp' (num hC) (num hV)
    (all2_map_fst (fun o y h => num h) hYs) hys' c1
  have e1' := scanMono Γ M c1 _ _ e1 (max N M) (Nat.le_max_right _ _)
  obtain ⟨st', efin⟩ := hcall (max N M) (Nat.le_max_left _ _) _ (by
    rw [toks_th, mark_eq, List.map_cons, map_tupToks]; exact e1')
  exact ⟨_, o', st', c', efin, ho'⟩

/-- `TH ( TH ( … S … ) )`, outermost first. -/
def nest : List (Tok × Tok × Tok) → List Tok → List Tok
  | [], S => S
  | (t, l, r) :: ls, S => t :: l :: (nest ls S ++ [r])

/-- The recursion's values: `v₀`, then `g(k, vₖ, ȳ)`. -/
def recV (g : Term) (ys : List Nat) (v0 : Nat) : Nat → Nat
  | 0 => v0
  | k + 1 => g.eval (k :: recV g ys v0 k :: ys)

theorem nest_shape {S : List Tok} (hS : ArgShape S) {π : List Code} :
    ∀ ls : List (Tok × Tok × Tok), (∀ q ∈ ls, q.1.s = fullName π .TH ∧ q.2.1.s = "(" ∧ q.2.2.s = ")") →
      ArgShape (nest ls S)
  | [], _ => hS
  | (t, l, r) :: ls, h => by
    obtain ⟨h1, h2, h3⟩ := h (t, l, r) (by simp)
    have := argShape_wrap (t := t) (l := l) (r := r) (by rw [h1]; exact fullName_ne_rp _ _) (by rw [h1]; exact fullName_ne_lp _ _)
      (by rw [h1]; exact fullName_ne_comma _ _) h2 h3 (nest_shape hS ls (fun q hq => h q (by simp [hq])))
    simpa [nest] using this

/-- **`n` levels.** -/
theorem th_nest (Γ : Env) (hp : PunctFree Γ) {f g : Term} {π : List Code} (hR : Realizes Γ (.prec f g) π)
    (hga : g.arity = f.arity + 2) (IHg : NodeOK Γ g (π ++ [.r])) {L : List Helper} (hTH : Helper.TH ∉ L)
    (hSTEP : Helper.STEP ∉ L) {S : List Tok} {v0 : Nat} {ys : List Nat} (hys : ys.length = f.arity)
    (hS : IsTuple 0 v0 ys S) :
    ∀ ls : List (Tok × Tok × Tok), (∀ q ∈ ls, q.1.s = fullName π .TH ∧ In π L q.1.H ∧ q.2.1.s = "(" ∧ q.2.2.s = ")") →
      ∀ c0, ∃ M o st c', scan Γ M c0 (nest ls S) = some (o, st, c') ∧ IsTuple ls.length (recV g ys v0 ls.length) ys o
  | [], _, c0 => ⟨_, S, [], c0, scan_nameFree' (isTuple_nameFree hp hS) c0, hS⟩
  | (t, l, r) :: ls, h, c0 => by
    obtain ⟨h1, h2, h3, h4⟩ := h (t, l, r) (by simp)
    have hrest : ∀ q ∈ ls, q.1.s = fullName π .TH ∧ In π L q.1.H ∧ q.2.1.s = "(" ∧ q.2.2.s = ")" :=
      fun q hq => h q (by simp [hq])
    have hT : ArgShape (nest ls S) := nest_shape (isTuple_shape hS) ls (fun q hq => let e := hrest q hq; ⟨e.1, e.2.2⟩)
    have hTe : ExpandsP Γ (nest ls S) (IsTuple ls.length (recV g ys v0 ls.length) ys) := by
      intro c1
      obtain ⟨M, o, st, c', e, ho⟩ := th_nest Γ hp hR hga IHg hTH hSTEP hys hS ls hrest c1
      exact ⟨M, finalize o, st, c', by simp [expand, e], isTuple_map ho _ (fun t => rfl)⟩
    obtain ⟨M, o, st, c', e, ho⟩ := th_level Γ hp hR hga IHg hTH hSTEP (sep := comma) hys h1 h2 h3 rfl h4 hT hTe c0
    exact ⟨M, o, st, c', by simpa [callToks, joinArgs, nest] using e, by simpa [recV] using ho⟩

end PP

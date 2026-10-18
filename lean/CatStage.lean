/-
  Theorem 10, recursion, stage G: `CAT_( (TH ( )ⁿ S )ⁿ Z , _END )` → the recursion's tuple.
-/
import ThNest

namespace PP

theorem pair_split (a b : String) : ∀ (n : Nat) (E : List Tok), E.map (·.s) = (List.replicate n [a, b]).flatten →
    ∃ P : List (Tok × Tok), E = P.flatMap (fun p => [p.1, p.2]) ∧ P.length = n ∧ ∀ p ∈ P, p.1.s = a ∧ p.2.s = b
  | 0, E, h => ⟨[], by simpa using h, rfl, by simp⟩
  | n + 1, E, h => by
    rw [List.replicate_succ, List.flatten_cons] at h
    match E, h with
    | p :: q :: E', h =>
      simp only [List.map_cons, List.cons_append, List.nil_append, List.cons.injEq] at h
      obtain ⟨hp, hq, h'⟩ := h
      obtain ⟨P, rfl, hl, hP⟩ := pair_split a b n E' h'
      refine ⟨(p, q) :: P, by simp, by simp [hl], ?_⟩
      intro x hx; simp at hx; rcases hx with rfl | hx
      · exact ⟨hp, hq⟩
      · exact hP x hx
    | [], h => simp at h
    | [_], h => simp at h

theorem rp_split (z : String) : ∀ (n : Nat) (E : List Tok), E.map (·.s) = List.replicate n ")" ++ [z] →
    ∃ (R : List Tok) (Z : Tok), E = R ++ [Z] ∧ R.length = n ∧ (∀ r ∈ R, r.s = ")") ∧ Z.s = z
  | 0, E, h => by
    match E, h with
    | [Z], h => exact ⟨[], Z, rfl, rfl, by simp, by simpa using h⟩
    | [], h => simp at h
    | _ :: _ :: _, h => simp at h
  | n + 1, E, h => by
    match E, h with
    | r :: E', h =>
      simp only [List.replicate_succ, List.map_cons, List.cons_append, List.cons.injEq] at h
      obtain ⟨hr, h'⟩ := h
      obtain ⟨R, Z, rfl, hl, hR, hZ⟩ := rp_split z n E' h'
      refine ⟨r :: R, Z, rfl, by simp [hl], ?_, hZ⟩
      intro x hx; simp at hx; rcases hx with rfl | hx
      · exact hr
      · exact hR x hx
    | [], h => simp at h

theorem nest_of (S : List Tok) : ∀ (P : List (Tok × Tok)) (R : List Tok), P.length = R.length →
    P.flatMap (fun p => [p.1, p.2]) ++ S ++ R = nest (List.zipWith (fun p r => (p.1, p.2, r)) P R.reverse) S
  | [], [], _ => by simp [nest]
  | p :: P, R, h => by
    obtain ⟨R', r, rfl⟩ : ∃ R' r, R = R' ++ [r] := by
      rcases List.eq_nil_or_concat R with h' | ⟨R', r, h'⟩
      · subst h'; simp at h
      · exact ⟨R', r, by rw [h']; simp⟩
    have h2 : P.length = R'.length := by simp at h; omega
    have := nest_of S P R' h2
    simp only [List.flatMap_cons, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.zipWith_cons_cons, nest]
    rw [← this]; simp
  | [], _ :: _, h => by simp at h

theorem map_nest (f : Tok → Tok) (S : List Tok) : ∀ ls : List (Tok × Tok × Tok),
    (nest ls S).map f = nest (ls.map fun q => (f q.1, f q.2.1, f q.2.2)) (S.map f)
  | [] => rfl
  | (t, l, r) :: ls => by simp [nest, map_nest f S ls]

theorem lastOK_tuple {Γ : Env} (hp : PunctFree Γ) {c v : Nat} {ys : List Nat} {o : List Tok} (h : IsTuple c v ys o) :
    LastOK Γ o := by
  obtain ⟨lp, sep, rp, C, V, Ys, rfl, _, _, hrp, _⟩ := h
  intro x hx; right; intro a w b e
  have h2 : (tupToks lp sep rp C V Ys).getLast? = some rp := by
    unfold tupToks; rw [List.getLast?_concat]
  rw [h2] at hx; cases hx; rw [hrp, hp.2.1] at e; cases e

theorem mem_zipWith3 : ∀ {P : List (Tok × Tok)} {R : List Tok} {q : Tok × Tok × Tok},
    q ∈ List.zipWith (fun p r => (p.1, p.2, r)) P R → ∃ p ∈ P, ∃ r ∈ R, q = (p.1, p.2, r)
  | [], _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | p :: P, r :: R, q, h => by
    simp only [List.zipWith_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨p, by simp, r, by simp, rfl⟩
    · obtain ⟨p', hp', r', hr', e⟩ := mem_zipWith3 h
      exact ⟨p', by simp [hp'], r', by simp [hr'], e⟩

/-- **`CAT_( (TH ( )ⁿ S )ⁿ Z , _END )`.** -/
theorem catu_stage (Γ : Env) (hp : PunctFree Γ) {f g : Term} {π : List Code} (hR : Realizes Γ (.prec f g) π)
    (hga : g.arity = f.arity + 2) (IHg : NodeOK Γ g (π ++ [.r])) {L : List Helper}
    (hL : ∀ y ∈ L, y ≠ .CATu ∧ y ≠ .TH ∧ y ≠ .STEP ∧ y ≠ .BRAEND ∧ y ≠ .BRBEND)
    {x lp sep rp e Z : Tok} {P : List (Tok × Tok)} {S R : List Tok} {n v0 : Nat} {ys : List Nat}
    (hx : x.s = fullName π .CATu) (hxH : In π L x.H) (hlp : lp.s = "(") (hsep : sep.s = ",") (hrp : rp.s = ")")
    (hrpH : In π L rp.H) (hP : ∀ p ∈ P, p.1.s = fullName π .TH ∧ p.2.s = "(" ∧ In π L p.1.H) (hPl : P.length = n)
    (hS : IsTuple 0 v0 ys S) (hys : ys.length = f.arity) (hRr : ∀ r ∈ R, r.s = ")") (hRl : R.length = n)
    (hZ : Z.s = if n % 2 = 0 then fullName π .BRA else fullName π .BRB) (hZH : In π L Z.H) (he : e.s = "_END")
    (heH : In π L e.H) (c : Nat) :
    ∃ M o st c', scan Γ M c (callToks x lp sep rp [P.flatMap (fun p => [p.1, p.2]) ++ S ++ R ++ [Z], [e]]) =
      some (o, st, c') ∧ IsTuple n (recV g ys v0 n) ys o := by
  have nCATu : Helper.CATu ∉ L := fun h => (hL _ h).1 rfl
  have nTH : Helper.TH ∉ L := fun h => (hL _ h).2.1 rfl
  have nSTEP : Helper.STEP ∉ L := fun h => (hL _ h).2.2.1 rfl
  let ZE : Helper := if n % 2 = 0 then .BRAEND else .BRBEND
  have nZE : ZE ∉ L := by
    by_cases hn : n % 2 = 0
    · simp only [ZE, hn, ite_true]; intro h; exact (hL _ h).2.2.2.1 rfl
    · simp only [ZE, hn, ite_false]; intro h; exact (hL _ h).2.2.2.2 rfl
  have nZE' : ZE ≠ .CATu := by by_cases hn : n % 2 = 0 <;> simp [ZE, hn]
  have hpaste : pasted Z.s e.s = some (fullName π ZE) := by
    rw [hZ, he]; by_cases h : n % 2 = 0
    · simp only [h, ite_true, ZE]; exact pasted_end π .BRA .BRAEND (by decide)
    · simp only [h, ite_false, ZE]; exact pasted_end π .BRB .BRBEND (by decide)
  let ls := List.zipWith (fun p r => (p.1, p.2, r)) P R.reverse
  have hnest : P.flatMap (fun p => [p.1, p.2]) ++ S ++ R = nest ls S := nest_of S P R (by rw [hPl, hRl])
  have hls : ∀ q ∈ ls, q.1.s = fullName π .TH ∧ In π L q.1.H ∧ q.2.1.s = "(" ∧ q.2.2.s = ")" := by
    intro q hq
    obtain ⟨p, hp', r, hr', rfl⟩ := mem_zipWith3 hq
    obtain ⟨h1, h2, h3⟩ := hP p hp'
    exact ⟨h1, h3, h2, hRr r (List.mem_reverse.mp hr')⟩
  have hA : ArgShape (P.flatMap (fun p => [p.1, p.2]) ++ S ++ R ++ [Z]) := by
    rw [hnest]; unfold ArgShape
    rw [walk_append, nest_shape (isTuple_shape hS) ls (fun q hq => let h := hls q hq; ⟨h.1, h.2.2⟩)]
    have h1 : (Z.s == ")") = false := by rw [hZ]; split <;> simpa using fullName_ne_rp _ _
    have h2 : (Z.s == "(") = false := by rw [hZ]; split <;> simpa using fullName_ne_lp _ _
    have h3 : (Z.s == ",") = false := by rw [hZ]; split <;> simpa using fullName_ne_comma _ _
    simp [walk, h1, h2, h3]
  have heshape : ArgShape [e] := by unfold ArgShape; rw [walk_spell]; simp [walkS, he]
  -- after the paste, marked
  let K := x.s :: inter x.H rp.H
  have hK : In π (.CATu :: L) K := by show In π (.CATu :: L) (x.s :: inter x.H rp.H); rw [hx]; exact in_mark hxH _ _
  let mk := markOne c K
  obtain ⟨M, o, st, c', e1, ho⟩ := th_nest Γ hp hR hga IHg (L := .CATu :: L) (by simp [nTH]) (by simp [nSTEP])
    hys (isTuple_map hS mk (fun t => rfl)) (ls.map fun q => (mk q.1, mk q.2.1, mk q.2.2))
    (by
      intro q hq; obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
      obtain ⟨h1, h2, h3, h4⟩ := hls q0 hq0
      exact ⟨h1, in_markOne hK (in_mono (fun y hy => by simp [hy]) h2) c, h3, h4⟩) (c + 1)
  have hZE : Γ.find (fullName π ZE) = some (.obj []) := by simp only [ZE]; split <;> exact find_prec hR _
  let zt := mk { s := fullName π ZE, H := inter Z.H e.H }
  have hzt : zt.s ∉ zt.H := not_mem_of_in (in_markOne hK (in_mono (fun y hy => by simp [hy]) (in_inter hZH _)) c)
    (by simp [nZE, nZE'])
  have ez := scan_obj_step Γ 1 c' zt [] hzt hZE ([], [], c' + 1) [] ([], [], c' + 1) (by simp [subst, substFrom])
    (by simp [paste, paste.go]) (by simp [mark, scan])
  have e2 := scan_frame2 Γ _ [zt] M (c + 1) (o, st, c') e1 (lastOK_tuple hp ho) _ _ ez
  obtain ⟨st', e3⟩ := paste_call Γ (by rw [hx]; exact find_prec hR .CATu) (by rw [hx]; exact not_mem_of_in hxH nCATu)
    hlp hsep hrp hA heshape hpaste (rest := []) (n := M + (1 + 1)) (c := c) (q := (o ++ [], _, c' + 1)) (by
      rw [List.append_nil, mark_eq, List.map_append, hnest, map_nest]; exact e2)
  have hlen : (ls.map fun q => (mk q.1, mk q.2.1, mk q.2.2)).length = n := by simp [ls, hPl, hRl]
  rw [hlen] at ho
  exact ⟨_, o, st', c' + 1, by simpa [callToks] using e3, ho⟩

end PP

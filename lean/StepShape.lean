/-
  Theorem 10, recursion, stage F preparation: tuples `( c̄ , v̄ , ȳ )`, depths, and the shape of
  `STEP`'s replacement.
-/
import AStage

namespace PP

/-- A tuple of numerals, its commas one token. -/
def tupToks (lp sep rp : Tok) (C V : List Tok) (Ys : List (List Tok)) : List Tok :=
  lp :: joinArgs sep (C :: V :: Ys) ++ [rp]

/-- `E` is the tuple `( c̄ , v̄ , ȳ )`. -/
def IsTuple (c v : Nat) (ys : List Nat) (E : List Tok) : Prop :=
  ∃ lp sep rp C V Ys, E = tupToks lp sep rp C V Ys ∧ lp.s = "(" ∧ sep.s = "," ∧ rp.s = ")" ∧ IsNum C c ∧
    IsNum V v ∧ All2 (fun Y y => IsNum Y y) Ys ys

theorem walkS_shift : ∀ (l : List String) (d d' e : Nat), walkS d l = some d' → walkS (d + e) l = some (d' + e)
  | [], d, d', e, h => by simp [walkS] at h; subst h; rfl
  | s :: l, d, d', e, h => by
    unfold walkS at h ⊢
    by_cases h1 : (s == ")") = true
    · by_cases h2 : (d == 0) = true
      · simp [h1, h2] at h
      · have h2' : (d + e == 0) = false := by simp at h2 ⊢; omega
        simp only [h1, h2, h2', ite_true, ite_false, Bool.false_eq_true] at h ⊢
        have := walkS_shift l (d - 1) d' e h
        rwa [show d + e - 1 = d - 1 + e by simp at h2; omega]
    · by_cases h3 : (s == "(") = true
      · simp only [h1, h3, ite_true, ite_false, Bool.false_eq_true] at h ⊢
        have := walkS_shift l (d + 1) d' e h
        rwa [show d + e + 1 = d + 1 + e by omega]
      · simp only [h1, h3, ite_false, Bool.false_eq_true] at h ⊢
        by_cases h4 : (s == "," && d == 0) = true
        · simp [h4] at h
        · have h4' : (s == "," && d + e == 0) = false := by
            simp at h4 ⊢; intro hs; have := h4 hs; omega
          simp only [h4, h4', ite_false, Bool.false_eq_true] at h ⊢
          exact walkS_shift l d d' e h

theorem walk_shift {A : List Tok} (h : ArgShape A) (d : Nat) : walk d A = some d := by
  unfold ArgShape at h; rw [walk_spell] at h ⊢
  simpa using walkS_shift _ 0 0 d h

/-- A call `t ( A )` around an argument is an argument. -/
theorem argShape_wrap {t l r : Tok} (ht1 : t.s ≠ ")") (ht2 : t.s ≠ "(") (ht3 : t.s ≠ ",") (hl : l.s = "(")
    (hr : r.s = ")") {A : List Tok} (hA : ArgShape A) : ArgShape (t :: l :: A ++ [r]) := by
  unfold ArgShape
  have h1 : (t.s == ")") = false := by simpa using ht1
  have h2 : (t.s == "(") = false := by simpa using ht2
  have h3 : (t.s == ",") = false := by simpa using ht3
  simp only [List.cons_append, walk, h1, h2, h3, hl, Bool.false_eq_true, ite_false, Bool.false_and,
    beq_self_eq_true, ite_true]
  rw [walk_append, walk_shift hA 1]
  simp [walk, hr]

theorem argShape_tuple {lp sep rp : Tok} {C V : List Tok} {Ys : List (List Tok)} (hlp : lp.s = "(") (hsep : sep.s = ",")
    (hrp : rp.s = ")") (h : ∀ A ∈ C :: V :: Ys, ∃ v, IsNum A v) : ArgShape (tupToks lp sep rp C V Ys) := by
  unfold ArgShape tupToks
  rw [List.cons_append]
  have h0 : walk 0 (lp :: (joinArgs sep (C :: V :: Ys) ++ [rp])) = walk 1 (joinArgs sep (C :: V :: Ys) ++ [rp]) := by
    simp [walk, hlp]
  rw [h0, walk_append, walk_joinArgs sep hsep 1 (by decide) _ (fun A hA => by obtain ⟨v, hv⟩ := h A hA; exact walk_num hv 1)]
  simp [walk, hrp]

/-! `tailB`. -/

theorem paramIdx_tailB : ∀ (ps : List Nat), paramIdx (tailB (ps.map prm)) = ps
  | [] => rfl
  | p :: ps => by simp [tailB, prm, tk, paramIdx] at *; exact paramIdx_tailB ps

theorem toks_tailB : ∀ (ps : List Nat) (outs : List (List Tok)), outs.length = ps.length →
    toks (plainOut (tailB (ps.map prm)) outs) = outs.flatMap fun o => comma :: o
  | [], [], _ => by simp [tailB, plainOut, toks]
  | p :: ps, o :: outs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    have ih := toks_tailB ps outs h
    simp only [tailB, List.map_cons, List.flatMap_cons, tk, prm, List.cons_append, List.nil_append, plainOut,
      toks_t] at ih ⊢
    rw [toks_map_t, ih]; rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem prms_eq (m s : Nat) : prms m s = ((List.range m).map (s + ·)).map prm := by simp [prms, Function.comp_def]

theorem joinArgs_cons_flat (sep : Tok) : ∀ (a : List Tok) (l : List (List Tok)),
    joinArgs sep (a :: l) = a ++ l.flatMap fun o => sep :: o
  | a, [] => by simp [joinArgs]
  | a, b :: l => by rw [joinArgs_cons_cons, joinArgs_cons_flat sep b l]; simp

/-- `STEP`'s body. -/
def stepBody (π : List Code) (m : Nat) : List BTok :=
  [tk "(", prm 0, tk "(", tk "~", tk ")", tk ",", nm (π ++ [.r]) .self, tk "(", prm 0, tk ",", prm 1] ++
    tailB (prms m 2) ++ [tk ")"] ++ tailB (prms m 2) ++ [tk ")"]

theorem precDef_step (m : Nat) (π : List Code) : precDef m π .STEP = .fn (m + 2) false (stepBody π m) := rfl

theorem paramIdx_step (π : List Code) (m : Nat) :
    paramIdx (stepBody π m) = [0, 0, 1] ++ (List.range m).map (2 + ·) ++ (List.range m).map (2 + ·) := by
  simp only [stepBody, paramIdx_append, prms_eq, paramIdx_tailB]
  simp [nm, tk, prm, paramIdx]

theorem toks_step (π : List Code) (m : Nat) (c1 c2 v : List Tok) (Y1 Y2 : List (List Tok)) (h1 : Y1.length = m)
    (h2 : Y2.length = m) :
    toks (plainOut (stepBody π m) ([c1, c2, v] ++ Y1 ++ Y2)) =
      { s := "(" } :: (c1 ++ [{ s := "(" }, { s := "~" }, { s := ")" }, comma] ++
        callToks { s := fullName (π ++ [.r]) .self } { s := "(" } comma { s := ")" } (c2 :: v :: Y1) ++
        (Y2.flatMap fun o => comma :: o) ++ [{ s := ")" }]) := by
  unfold stepBody
  rw [prms_eq]
  let B1 : List BTok := [tk "(", prm 0, tk "(", tk "~", tk ")", tk ",", nm (π ++ [.r]) .self, tk "(", prm 0, tk ",", prm 1]
  let T : List BTok := tailB (((List.range m).map (2 + ·)).map prm)
  have pB1 : paramIdx B1 = [0, 0, 1] := by simp [B1, nm, tk, prm, paramIdx]
  have pT : paramIdx T = (List.range m).map (2 + ·) := paramIdx_tailB _
  have pR : paramIdx [tk ")"] = [] := rfl
  rw [show [c1, c2, v] ++ Y1 ++ Y2 = (((([c1, c2, v] ++ Y1) ++ []) ++ Y2) ++ []) by simp]
  rw [plainOut_append (((B1 ++ T) ++ [tk ")"]) ++ T) [tk ")"] ((([c1, c2, v] ++ Y1) ++ []) ++ Y2) [] (by
      simp only [paramIdx_append, pB1, pT, pR]; simp [h1, h2])]
  rw [plainOut_append ((B1 ++ T) ++ [tk ")"]) T (([c1, c2, v] ++ Y1) ++ []) Y2 (by
      simp only [paramIdx_append, pB1, pT, pR]; simp [h1])]
  rw [plainOut_append (B1 ++ T) [tk ")"] ([c1, c2, v] ++ Y1) [] (by simp only [paramIdx_append, pB1, pT]; simp [h1])]
  rw [plainOut_append B1 T [c1, c2, v] Y1 (by rw [pB1]; rfl)]
  have hT1 : toks (plainOut T Y1) = Y1.flatMap fun o => comma :: o := toks_tailB _ Y1 (by simp [h1])
  have hT2 : toks (plainOut T Y2) = Y2.flatMap fun o => comma :: o := toks_tailB _ Y2 (by simp [h2])
  simp only [toks_append]; rw [hT1, hT2]
  simp only [B1, nm, tk, prm, plainOut, toks_t, toks_map_t]
  simp [toks, tokOf, callToks, joinArgs_cons_flat, comma]

end PP

/-
  Theorem 10, the node lemma for primitive recursion.
-/
import SelStage

namespace PP

def precBody (π : List Code) (m : Nat) : List BTok :=
  [nm π .SEL, tk "(", nm π .ITER, tk "(", prm 0, tk ",", tk "(", tk ",", nm (π ++ [.f]) .self, tk "("] ++
    joinB ((prms m 1).map ([·])) ++ [tk ")"] ++ tailB (prms m 1) ++ [tk ")", tk ")", tk ")"]

theorem precDef_self (m : Nat) (π : List Code) : precDef m π .self = .fn (m + 1) false (precBody π m) := rfl

/-- The base: `( , f ( ȳ ) , ȳ )`. -/
def baseToks (π : List Code) (Y1 Y2 : List (List Tok)) : List Tok :=
  { s := "(" } :: comma :: (callToks { s := fullName (π ++ [.f]) .self } { s := "(" } comma { s := ")" } Y1 ++
    ((Y2.flatMap fun o => comma :: o) ++ [{ s := ")" }]))

theorem prms_single_off (m s : Nat) : (prms m s).map ([·]) = ((List.range m).map (s + ·)).map fun i => [prm i] := by
  simp [prms, Function.comp_def]

theorem paramIdx_prec (π : List Code) (m : Nat) :
    paramIdx (precBody π m) = [0] ++ (List.range m).map (1 + ·) ++ (List.range m).map (1 + ·) := by
  unfold precBody
  simp only [paramIdx_append]
  rw [prms_single_off, paramIdx_joinB_single, prms_eq, paramIdx_tailB]
  simp [nm, tk, prm, paramIdx]

theorem toks_prec (π : List Code) (m : Nat) (oN : List Tok) (Y1 Y2 : List (List Tok)) (h1 : Y1.length = m)
    (h2 : Y2.length = m) :
    toks (plainOut (precBody π m) ([oN] ++ Y1 ++ Y2)) =
      callToks { s := fullName π .SEL } { s := "(" } comma { s := ")" }
        [callToks { s := fullName π .ITER } { s := "(" } comma { s := ")" } [oN, baseToks π Y1 Y2]] := by
  unfold precBody
  let B1 : List BTok := [nm π .SEL, tk "(", nm π .ITER, tk "(", prm 0, tk ",", tk "(", tk ",", nm (π ++ [.f]) .self, tk "("]
  let J : List BTok := joinB ((prms m 1).map ([·]))
  let T : List BTok := tailB (prms m 1)
  have pB1 : paramIdx B1 = [0] := by simp [B1, nm, tk, prm, paramIdx]
  have pJ : paramIdx J = (List.range m).map (1 + ·) := by simp only [J, prms_single_off, paramIdx_joinB_single]
  have pT : paramIdx T = (List.range m).map (1 + ·) := by simp only [T, prms_eq, paramIdx_tailB]
  rw [show [oN] ++ Y1 ++ Y2 = ((([oN] ++ Y1) ++ []) ++ Y2) ++ [] by simp]
  rw [plainOut_append (((B1 ++ J) ++ [tk ")"]) ++ T) [tk ")", tk ")", tk ")"] ((([oN] ++ Y1) ++ []) ++ Y2) [] (by
      simp only [paramIdx_append, pB1, pJ, pT]; simp [tk, paramIdx, h1, h2])]
  rw [plainOut_append ((B1 ++ J) ++ [tk ")"]) T (([oN] ++ Y1) ++ []) Y2 (by
      simp only [paramIdx_append, pB1, pJ]; simp [tk, paramIdx, h1])]
  rw [plainOut_append (B1 ++ J) [tk ")"] ([oN] ++ Y1) [] (by simp only [paramIdx_append, pB1, pJ]; simp [h1])]
  rw [plainOut_append B1 J [oN] Y1 (by rw [pB1]; rfl)]
  have hJ : toks (plainOut J Y1) = joinArgs comma Y1 := by
    simp only [J, prms_single_off]; exact toks_joinB_single _ Y1 (by simp [h1])
  have hT : toks (plainOut T Y2) = Y2.flatMap fun o => comma :: o := by
    simp only [T, prms_eq]; exact toks_tailB _ Y2 (by simp [h2])
  simp only [toks_append]; rw [hJ, hT]
  simp only [B1, nm, tk, prm, plainOut, toks_t, toks_map_t]
  simp [toks, tokOf, callToks, joinArgs, baseToks, comma]

theorem map_baseToks (f : Tok → Tok) (π : List Code) (Y1 Y2 : List (List Tok)) :
    (baseToks π Y1 Y2).map f = f { s := "(" } :: f comma :: (callToks (f { s := fullName (π ++ [.f]) .self }) (f { s := "(" })
      (f comma) (f { s := ")" }) (Y1.map (List.map f)) ++ (((Y2.map (List.map f)).flatMap fun o => f comma :: o) ++
      [f { s := ")" }])) := by
  simp [baseToks, callToks, map_joinArgs, map_flatMap_cons]

/-- **The base `( , f ( ȳ ) , ȳ )`** expands to the tuple `( 0 , f(ȳ) , ȳ )`. -/
theorem base_stage (Γ : Env) (hp : PunctFree Γ) {f g : Term} {π : List Code}
    (IHf : NodeOK Γ f (π ++ [.f])) {L : List Helper} {K : List Name} (hK : In π L K) {Y1 Y2 : List (List Tok)}
    {ys : List Nat} (hY1 : All2 (fun Y y => IsNum Y y) Y1 ys) (hY2 : All2 (fun Y y => IsNum Y y) Y2 ys)
    (hys : ys.length = f.arity) (cm : Nat) :
    ExpandsP Γ ((baseToks π Y1 Y2).map (markOne cm K)) (IsTuple 0 (f.eval ys) ys) := by
  intro c0
  let mk := markOne cm K
  have num : ∀ {o : List Tok} {w : Nat}, IsNum o w → IsNum (o.map mk) w := fun h => isNum_markAll h cm K
  have hY1m : All2 (fun Y y => IsNum Y y) (Y1.map (List.map mk)) ys := all2_map_fst (fun o y h => num h) hY1
  have hY2m : All2 (fun Y y => IsNum Y y) (Y2.map (List.map mk)) ys := all2_map_fst (fun o y h => num h) hY2
  obtain ⟨N, W, st, c1, eF, hW⟩ := IHf (mk { s := fullName (π ++ [.f]) .self }) (mk { s := "(" }) (mk comma)
    (mk { s := ")" }) (Y1.map (List.map mk)) ys rfl (fun hm => child_not_in hK .f (mem_markOne_body.mp hm)) rfl rfl rfl
    (by have := all2_length hY1m; omega) (argsOK_nums hp hY1m)
    (fun n hn => in_child hK .f n (mem_markOne_body.mp (mem_inter.mp hn).1)) c0
  let rest := ((Y2.map (List.map mk)).flatMap fun o => mk comma :: o) ++ [mk { s := ")" }]
  have hrest : NameFree Γ rest := nameFree_append (nameFree_flat hp rfl (nameFree_nums hp hY2m))
    (by intro t ht; simp at ht; subst ht; exact hp.2.1)
  have e1 := scan_frame2 Γ _ rest N c0 (W, st, c1) eF (lastOK_num hp hW) _ _ (scan_nameFree' hrest c1)
  have e2 := scan_nameFree_prefix Γ [mk { s := "(" }, mk comma] (by
    intro t ht; simp at ht; rcases ht with rfl | rfl
    · exact hp.1
    · exact hp.2.2.1) e1
  refine ⟨_, finalize ([mk { s := "(" }, mk comma] ++ (W ++ rest)), _, _, by
    rw [map_baseToks]; simp only [expand]; rw [show mk { s := "(" } :: mk comma :: (callToks (mk { s := fullName (π ++ [.f]) .self })
      (mk { s := "(" }) (mk comma) (mk { s := ")" }) (Y1.map (List.map mk)) ++ rest) =
      [mk { s := "(" }, mk comma] ++ (callToks (mk { s := fullName (π ++ [.f]) .self }) (mk { s := "(" }) (mk comma)
      (mk { s := ")" }) (Y1.map (List.map mk)) ++ rest) from rfl, e2]; rfl, ?_⟩
  refine isTuple_map ⟨mk { s := "(" }, mk comma, mk { s := ")" }, [], W, Y2.map (List.map mk), ?_, rfl, rfl, rfl,
    (show IsNum [] 0 from rfl), hW, hY2m⟩ _ (fun t => rfl)
  simp [tupToks, joinArgs_cons_flat, rest]

theorem all2_range_off1 {P : List Tok → Nat → Prop} {m : Nat} {Y : List (List Tok)} {a : Nat} {ys : List Nat}
    (hys : ys.length = m) (h : All2 (fun j o => P o ((a :: ys).getD j 0)) ((List.range m).map (1 + ·)) Y) :
    All2 P Y ys := by
  obtain ⟨hl, hi⟩ := all2_iff.mp h
  refine all2_iff.mpr ⟨by simp at hl; omega, fun i h1 h2 => ?_⟩
  have := hi i (by simp; omega) h1
  simp only [List.getElem_map, List.getElem_range] at this
  rwa [show 1 + i = i + 1 by omega, List.getD_cons_succ, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h2, Option.getD_some] at this

/-- A call on arguments is an argument. -/
theorem argShape_callA {x lp sep rp : Tok} (hx1 : x.s ≠ ")") (hx2 : x.s ≠ "(") (hx3 : x.s ≠ ",") (hlp : lp.s = "(")
    (hsep : sep.s = ",") (hrp : rp.s = ")") (as : List (List Tok)) (h : ∀ A ∈ as, ArgShape A) :
    ArgShape (callToks x lp sep rp as) := by
  unfold ArgShape callToks
  have hx1' : (x.s == ")") = false := by simpa using hx1
  have hx2' : (x.s == "(") = false := by simpa using hx2
  have hx3' : (x.s == ",") = false := by simpa using hx3
  simp only [walk, hx1', hx2', hx3', hlp, Bool.false_eq_true, ite_false, Bool.false_and, beq_self_eq_true, ite_true]
  rw [walk_append, walk_joinArgs sep hsep 1 (by decide) as (fun A hA => walk_shift (h A hA) 1)]
  simp [walk, hrp]

theorem walk_flatComma (sep : Tok) (hsep : sep.s = ",") (d : Nat) (hd : d ≠ 0) :
    ∀ (Y : List (List Tok)), (∀ o ∈ Y, ArgShape o) → walk d (Y.flatMap fun o => sep :: o) = some d
  | [], _ => rfl
  | o :: Y, h => by
    simp only [List.flatMap_cons, List.cons_append]
    have hd' : (d == 0) = false := by simpa using hd
    simp only [walk, hsep]
    simp only [show ("," == ")") = false from rfl, show ("," == "(") = false from rfl, beq_self_eq_true, hd',
      Bool.and_false, Bool.false_eq_true, ite_false]
    rw [walk_append, walk_shift (h o (by simp)) d]
    exact walk_flatComma sep hsep d hd Y (fun o' ho' => h o' (by simp [ho']))

theorem argShape_base {π : List Code} {mk : Tok → Tok} (hmk : ∀ t, (mk t).s = t.s) {Y1 Y2 : List (List Tok)}
    (h1 : ∀ o ∈ Y1, ArgShape o) (h2 : ∀ o ∈ Y2, ArgShape o) :
    ArgShape (mk { s := "(" } :: mk comma :: (callToks (mk { s := fullName (π ++ [.f]) .self }) (mk { s := "(" })
      (mk comma) (mk { s := ")" }) Y1 ++ ((Y2.flatMap fun o => mk comma :: o) ++ [mk { s := ")" }]))) := by
  have hc := argShape_callA (x := mk { s := fullName (π ++ [.f]) .self }) (lp := mk { s := "(" }) (sep := mk comma)
    (rp := mk { s := ")" }) (by rw [hmk]; exact fullName_ne_rp _ _) (by rw [hmk]; exact fullName_ne_lp _ _)
    (by rw [hmk]; exact fullName_ne_comma _ _) (by rw [hmk]) (by rw [hmk]; rfl) (by rw [hmk]) Y1 h1
  unfold ArgShape at *
  simp only [walk, hmk, show ("(" == ")") = false from rfl, beq_self_eq_true, ite_true, Bool.false_eq_true, ite_false]
  simp only [show (comma.s == ")") = false from rfl, show (comma.s == "(") = false from rfl,
    show (comma.s == ",") = true from rfl, Bool.true_and, show ((1 : Nat) == 0) = false from rfl, ite_false,
    Bool.false_eq_true]
  rw [walk_append, walk_shift (by exact hc) 1]; simp only [Option.bind_some]
  rw [walk_append, walk_flatComma (mk comma) (by rw [hmk]; rfl) 1 (by decide) Y2 h2]
  simp [walk, hmk]

theorem recV_eq (g : Term) (ys : List Nat) (v0 : Nat) : ∀ n,
    recV g ys v0 n = Nat.rec (motive := fun _ => Nat) v0 (fun c v => g.eval (c :: v :: ys)) n
  | 0 => rfl
  | n + 1 => by simp only [recV]; rw [recV_eq g ys v0 n]

end PP

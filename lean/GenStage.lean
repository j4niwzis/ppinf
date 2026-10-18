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

end PP

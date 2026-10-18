/-
  Theorem 10, recursion, stage E: CAT's first argument `GEN ( n̄ ) S BRA n̄` scans to
  `(TH ( )ⁿ S )ⁿ Z`.
-/
import GenStage

namespace PP

/-- Names in it hide nothing of their own. -/
def NamesClear (o : List Tok) : Prop := ∀ t ∈ o, IsName t.s → t.s ∉ t.H

theorem lastOK_of_punct {Γ : Env} (hp : PunctFree Γ) {o : List Tok}
    (h : ∀ x, o.getLast? = some x → x.s = "(") : LastOK Γ o := by
  intro x hx; right; intro a v b e; rw [h x hx, hp.1] at e; cases e

theorem getLast_spell {o : List Tok} {l : List String} (h : o.map (·.s) = l) {x : Tok} (hx : o.getLast? = some x) :
    l.getLast? = some x.s := by
  rw [← h, List.getLast?_map, hx]; rfl

theorem a_stage (Γ : Env) (hp : PunctFree Γ) {f g : Term} {π : List Code} (hR : Realizes Γ (.prec f g) π)
    {L : List Helper} (hL : ∀ y ∈ L, y ≠ .GEN ∧ y ≠ .CAT2 ∧ y ≠ .CAT2u ∧ y ≠ .GA ∧ y ≠ .GB ∧ y ≠ .TH ∧ y ≠ .D1 ∧
      y ≠ .D0 ∧ y ≠ .OUT ∧ y ≠ .GAEND ∧ y ≠ .GBEND ∧ y ≠ .BRA ∧ y ≠ .BRB)
    {x lp sep rp bra : Tok} {Nm Nm2 S : List Tok} {n : Nat} (hx : x.s = fullName π .GEN) (hxH : In π L x.H)
    (hlp : lp.s = "(") (hsep : sep.s = ",") (hrp : rp.s = ")") (hrpH : In π L rp.H) (hN : IsNum Nm n)
    (hS : NameFree Γ S) (hb : bra.s = fullName π .BRA) (hbH : In π L bra.H) (hN2 : IsNum Nm2 n)
    (hN2H : ∀ t ∈ Nm2, InJ π L t.H) (c : Nat) :
    ∃ M o1 o2 st c', scan Γ M c (callToks x lp sep rp [Nm] ++ (S ++ bra :: Nm2)) = some (o1 ++ (S ++ o2), st, c') ∧
      o1.map (·.s) = (List.replicate n [fullName π .TH, "("]).flatten ∧
      o2.map (·.s) = List.replicate n ")" ++ [if n % 2 = 0 then fullName π .BRA else fullName π .BRB] ∧
      (∀ t ∈ o1, t.s ∉ t.H) ∧ ∀ t ∈ o2, t.s ∉ t.H := by
  obtain ⟨M1, o1, st1, c1, e1, ho1, hfin1⟩ := gen_stage Γ hp hR (fun y hy => let h := hL y hy;
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1⟩) hx hxH hlp hsep hrp hrpH hN c
  have nBRA : Helper.BRA ∉ L := fun h => (hL _ h).2.2.2.2.2.2.2.2.2.2.2.1 rfl
  have nBRB : Helper.BRB ∉ L := fun h => (hL _ h).2.2.2.2.2.2.2.2.2.2.2.2 rfl
  obtain ⟨G, hG, hGl, hGg⟩ := num_groups n Nm2 hN2
  obtain ⟨M2, o2, st2, c2, e2, ho2, hfin2⟩ := brapong Γ hp G (fullName π .BRA) (fullName π .BRB) bra c1
    (fun gr hgr => ⟨hGg gr hgr,
      not_mem_of_inJ (hN2H gr.2.2 (by rw [hG]; exact List.mem_flatMap.mpr ⟨gr, hgr, by simp⟩)) nBRA,
      not_mem_of_inJ (hN2H gr.2.2 (by rw [hG]; exact List.mem_flatMap.mpr ⟨gr, hgr, by simp⟩)) nBRB⟩)
    (find_prec hR .BRA) (find_prec hR .BRB) (fullName_ne_helper (by decide)) (fullName_ne_rp _ _) (fullName_ne_rp _ _) hb
    (by
      intro m hm; right
      rcases hbH m hm with ⟨y, hy, rfl⟩ | e
      · exact ⟨fullName_ne_helper (fun h => nBRA (h ▸ hy)), fullName_ne_helper (fun h => nBRB (h ▸ hy)), fullName_ne_rp _ _⟩
      · have nb : ∀ z, m ≠ fullName π z := fun z en => e.1 ⟨[], z, by simp [en]⟩
        obtain ⟨π', y', rfl⟩ := e.2
        exact ⟨nb _, nb _, fullName_ne_rp _ _⟩)
  have e2b : scan Γ M2 c1 (bra :: Nm2) = some (o2, st2, c2) := by rw [hG]; exact e2
  have e2' := scan_nameFree_prefix Γ S hS e2b
  have hlast : LastOK Γ o1 := by
    apply lastOK_of_punct hp
    intro y hy
    have := getLast_spell ho1 hy
    cases n with
    | zero => simp at this
    | succ n =>
      rw [List.replicate_succ', List.flatten_append] at this
      simp at this; exact this.symm
  have e3 := scan_frame2 Γ _ _ M1 c (o1, st1, c1) e1 hlast _ _ e2'
  exact ⟨_, o1, o2, _, _, e3, ho1, by rw [ho2, hGl], hfin1, hfin2⟩

end PP

/-
  Theorem 10, recursion, stage B: after the paste, `(TH D0 ( ))ⁿ X_END` scans to `(TH ( )ⁿ` --
  `TH` passed by (`D0` follows), `D0 ( )` → `(`, and `X_END` empty.
-/
import PrecCtx

namespace PP

def quadToks (G : List (Tok × Tok × Tok × Tok)) : List Tok := G.flatMap fun g => [g.1, g.2.1, g.2.2.1, g.2.2.2]

theorem d0stage (Γ : Env) (hp : PunctFree Γ) {π : List Code} {L : List Helper} (hTH : Helper.TH ∉ L) (hD0 : Helper.D0 ∉ L)
    {thAr : Nat} {thBody : List BTok} (hth : Γ.find (fullName π .TH) = some (.fn thAr false thBody))
    (hd0 : Γ.find (fullName π .D0) = some (.fn 0 false [tk "("])) {xe : Tok} (hxe : Γ.find xe.s = some (.obj []))
    (hxeH : xe.s ∉ xe.H) :
    ∀ (G : List (Tok × Tok × Tok × Tok)) (c : Nat),
      (∀ g ∈ G, g.1.s = fullName π .TH ∧ g.2.1.s = fullName π .D0 ∧ g.2.2.1.s = "(" ∧ g.2.2.2.s = ")" ∧
        In π L g.1.H ∧ In π L g.2.1.H ∧ In π L g.2.2.2.H) →
      ∃ N o st c', scan Γ N c (quadToks G ++ [xe]) = some (o, st, c') ∧
        o.map (·.s) = (List.replicate G.length [fullName π .TH, "("]).flatten ∧ ∀ t ∈ o, t.s ∉ t.H
  | [], c, _ => by
    have := scan_obj_step Γ 1 c xe [] hxeH hxe ([], [], c + 1) [] ([], [], c + 1) (by simp [subst, substFrom])
      (by simp [paste, paste.go]) (by simp [mark, scan])
    exact ⟨2, [], _, _, by simpa [quadToks] using this, rfl, by simp⟩
  | (th, d0, l, r) :: G, c, hG => by
    obtain ⟨hs1, hs2, hs3, hs4, hH1, hH2, hH4⟩ := hG (th, d0, l, r) (by simp)
    simp only at hs1 hs2 hs3 hs4 hH1 hH2 hH4
    obtain ⟨N, o, st, c', e, ho, hfin⟩ := d0stage Γ hp hTH hD0 hth hd0 hxe hxeH G (c + 1) (fun g hg => hG g (by simp [hg]))
    let K := d0.s :: inter d0.H r.H
    have hK : In π (.D0 :: L) K := by show In π (.D0 :: L) (d0.s :: inter d0.H r.H); rw [hs2]; exact in_mark hH2 .D0 r.H
    -- `(` from `D0`, emitted
    have s1 := scan_emit_none Γ (x := markOne c K { s := "(" }) hp.1 e
    -- `D0 ( )`
    obtain ⟨st2, s2⟩ := call_toks Γ (x := d0) (lp := l) (rp := r) (l := ["("]) (by rw [hs2]; exact hd0)
      (by rw [hs2]; exact not_mem_of_in hH2 hD0) hs3 (closeAt_empty hs4 _) bind_00 (n := N + 1) (c := c)
      (by rw [mark_strs]; exact s1)
    -- `TH`, passed by
    have s3 := scan_emit_fn Γ (x := th) (by rw [hs1]; exact hth) (by rw [hs2]; exact fullName_ne_lp _ _) (by simpa using s2)
    refine ⟨N + 1 + 1 + 1, _, _, c', by simpa [quadToks] using s3, ?_, ?_⟩
    · simp [hs1, markOne_s, ho, List.replicate_succ]
    · intro t ht
      simp only [List.mem_cons] at ht
      rcases ht with rfl | rfl | ht
      · rw [hs1]; exact not_mem_of_in hH1 hTH
      · exact name_ne_of_in (in_markOne hK (in_nil _ _) c) (fun π' y => fullName_ne_lp π' y)
      · exact hfin t ht

end PP

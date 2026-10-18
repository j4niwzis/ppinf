/-
  Theorem 10, recursion: the ping-pong `BRA n̄` -- each group `( ~ )` gives `)`, and the last
  of `BRA`/`BRB` is left: `)ⁿ Z`.
-/
import PingPong

namespace PP

def BRInv (A B : Name) (H : List Name) : Prop := ∀ n ∈ H, n = B ∨ (n ≠ A ∧ n ≠ B ∧ n ≠ ")")

theorem brapong (Γ : Env) (hp : PunctFree Γ) :
    ∀ (G : List (Tok × Tok × Tok)) (A B : Name) (x : Tok) (c : Nat),
      (∀ g ∈ G, Group g ∧ A ∉ g.2.2.H ∧ B ∉ g.2.2.H) →
      Γ.find A = some (.fn 0 true [tk ")", tk B]) → Γ.find B = some (.fn 0 true [tk ")", tk A]) →
      A ≠ B → A ≠ ")" → B ≠ ")" → x.s = A → BRInv A B x.H →
      ∃ Nf o st c', scan Γ Nf c (x :: groupToks G) = some (o, st, c') ∧
        o.map (·.s) = List.replicate G.length ")" ++ [if G.length % 2 = 0 then A else B] ∧
        ∀ t ∈ o, t.s ∉ t.H
  | [], A, B, x, c, _, hA, _, hAB, _, _, hx, hinv => by
    refine ⟨2, [x], [], c, scan_fn_last Γ (by rw [hx]; exact hA) 0 c, by simp [hx], ?_⟩
    intro t ht; simp at ht; subst ht
    intro hm; rw [hx] at hm
    rcases hinv A hm with e | e
    · exact hAB e
    · exact e.1 rfl
  | (l, t, r) :: G, A, B, x, c, hG, hA, hB, hAB, hAr', hBr', hx, hinv => by
    obtain ⟨⟨hl, ht, hr⟩, hAr, hBr⟩ := hG (l, t, r) (by simp)
    let K1 := A :: inter x.H r.H
    have mK1 : ∀ n ∈ K1, n = A ∨ (n ≠ A ∧ n ≠ B ∧ n ≠ ")") := by
      intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · left; rfl
      · obtain ⟨h1, h2⟩ := mem_inter.mp hn
        rcases hinv n h1 with rfl | e
        · exact absurd h2 hBr
        · right; exact e
    have hinv' : BRInv B A (markOne c K1 { s := B }).H := by
      intro n hn
      rcases mK1 n (mem_markOne_body.mp hn) with e | e
      · left; exact e
      · right; exact ⟨e.2.1, e.1, e.2.2⟩
    obtain ⟨Nf, o, st, c', e, ho, hfin⟩ := brapong Γ hp G B A (markOne c K1 { s := B }) (c + 1)
      (fun g hg => let h := hG g (by simp [hg]); ⟨h.1, h.2.2, h.2.1⟩) hB hA (Ne.symm hAB) hBr' hAr' rfl hinv'
    let rest := groupToks G
    have s1 := scan_emit_none Γ (x := markOne c K1 { s := ")" }) hp.2.1 e
    have ht1 : t.s ≠ ")" := by rw [ht]; decide
    have ht2 : t.s ≠ "(" := by rw [ht]; decide
    have ht3 : t.s ≠ "," := by rw [ht]; decide
    have hxA : x.s ∉ x.H := by
      intro hm; rw [hx] at hm
      rcases hinv A hm with e' | e'
      · exact hAB e'
      · exact e'.1 rfl
    obtain ⟨st2, s2⟩ := call_toks Γ (x := x) (lp := l) (rp := r) (l := [")", B])
      (by rw [hx]; exact hA) hxA hl (closeAt_tilde ht1 ht2 hr rest) (bind_va0 ht3) (n := Nf + 1) (c := c)
      (by rw [mark_strs, hx]; exact s1)
    refine ⟨Nf + 1 + 1, _, st2, c', s2, ?_, ?_⟩
    · simp only [List.map_cons, markOne_s, ho, List.length_cons, List.replicate_succ]
      rw [if_parity]; simp
    · intro u hu
      simp only [List.mem_cons] at hu
      rcases hu with rfl | hu
      · intro hm
        rcases mK1 _ (mem_markOne_body.mp hm) with e' | e'
        · exact hAr' e'.symm
        · exact e'.2.2 rfl
      · exact hfin u hu

end PP

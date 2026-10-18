/-
  Theorem 10, recursion: the ping-pong `GA n̄` -- each group `( ~ )` of `n̄` gives
  `TH D0 ( )`, and the last of `GA`/`GB` is left: `(TH D0 ( ))ⁿ X`.
-/
import ScanSteps

namespace PP

theorem noOp_map_t : ∀ (l : List Tok), NoOp (l.map RTok.t)
  | [] => trivial
  | _ :: l => by simpa [NoOp] using noOp_map_t l

/-- A call of a macro whose body is tokens only. -/
theorem call_toks (Γ : Env) {x lp rp : Tok} {ar : Nat} {va : Bool} {l : List String}
    (hf : Γ.find x.s = some (.fn ar va (l.map tk))) (hid : x.s ∉ x.H) (hlp : lp.s = "(")
    {inner rest : List Tok} (hc : closeAt 0 (inner ++ rp :: rest) [] = some (inner, rp, rest)) {named vaArg}
    (hb : bind ar va inner = some (named, vaArg)) {n c : Nat} {q}
    (h : scan Γ n (c + 1) (mark c (x.s :: inter x.H rp.H) (l.map fun s => { s }) ++ rest) = some q) :
    ∃ st, scan Γ (n + 1) c (x :: lp :: (inner ++ rp :: rest)) = some (q.1, st, q.2.2) := by
  have hr : subst Γ n (c + 1) (l.map tk) named vaArg = some (l.map fun s => RTok.t { s }, [], c + 1) := by
    unfold subst
    suffices ∀ (bs : List String) i, substFrom Γ n (l.map tk) (bs.map tk) i (c + 1) named vaArg =
        some (bs.map fun s => RTok.t { s }, [], c + 1) from this l 0
    intro bs; induction bs with
    | nil => intro i; simp [substFrom]
    | cons s bs ih => intro i; simp [substFrom, piece, tk, ih]
  have e : (l.map fun s => RTok.t { s }) = (l.map fun s => ({ s } : Tok)).map RTok.t := by simp
  have hp : paste (l.map fun s => RTok.t { s }) = some (l.map fun s => { s }) := by
    rw [e, paste_noop _ (noOp_map_t _), toks_map]
  exact ⟨_, scan_fn_step Γ n c x lp rp inner rest hid hf hlp hc named vaArg _ _ q hb hr hp h⟩

/-- A group `( ~ )` of a numeral. -/
def Group (g : Tok × Tok × Tok) : Prop := g.1.s = "(" ∧ g.2.1.s = "~" ∧ g.2.2.s = ")"

def groupToks (G : List (Tok × Tok × Tok)) : List Tok := G.flatMap fun g => [g.1, g.2.1, g.2.2]

/-- The names of the ping-pong, and what it needs of them. -/
structure PPNames (Γ : Env) where
  th : Name
  d1 : Name
  d0 : Name
  out : Name
  thAr : Nat
  thBody : List BTok
  hth : Γ.find th = some (.fn thAr false thBody)
  hd1 : Γ.find d1 = some (.fn 0 false [tk d0, tk out, tk "(", tk ")"])
  hd0 : Γ.find d0 = some (.fn 0 false [tk "("])
  hout : Γ.find out = some (.obj [])
  out_lp : out ≠ "("
  d1_lp : d1 ≠ "("
  d1_rp : d1 ≠ ")"
  d0_d1 : d0 ≠ d1
  out_d1 : out ≠ d1

/-- The hidden names a ping-pong head may carry: its partner, or nothing it needs. -/
def PPInv (N : PPNames Γ) (A B : Name) (H : List Name) : Prop :=
  ∀ n ∈ H, n = B ∨ (n ≠ A ∧ n ≠ B ∧ n ≠ N.th ∧ n ≠ N.d1 ∧ n ≠ N.d0 ∧ n ≠ N.out ∧ n ≠ "(" ∧ n ≠ ")")

theorem mark_strs (c : Nat) (K : List Name) (l : List String) :
    mark c K (l.map fun s => { s }) = l.map fun s => markOne c K { s } := by
  simp [mark_eq, Function.comp_def]

theorem closeAt_tilde {t r : Tok} (ht1 : t.s ≠ ")") (ht2 : t.s ≠ "(") (hr : r.s = ")") (rest : List Tok) :
    closeAt 0 ([t] ++ r :: rest) [] = some ([t], r, rest) := by
  have h1 : (t.s == ")") = false := by simpa using ht1
  have h2 : (t.s == "(") = false := by simpa using ht2
  simp [closeAt_cons, h1, h2, hr]

theorem closeAt_empty {r : Tok} (hr : r.s = ")") (rest : List Tok) : closeAt 0 ([] ++ r :: rest) [] = some ([], r, rest) := by
  simp [closeAt_cons, hr]

theorem bind_va0 {t : Tok} (ht : t.s ≠ ",") : bind 0 true [t] = some ([], [t]) := by
  have h : (t.s == ",") = false := by simpa using ht
  simp [bind, splitTop_cons, h, splitTop, afterCommas]

theorem bind_00 : bind 0 false [] = some ([], []) := by simp [bind, splitTop]

theorem if_parity (n : Nat) (A B : Name) :
    (if n % 2 = 0 then B else A) = (if (n + 1) % 2 = 0 then A else B) := by
  by_cases h : n % 2 = 0
  · have : (n + 1) % 2 ≠ 0 := by omega
    simp [h, this]
  · have : (n + 1) % 2 = 0 := by omega
    simp [h, this]

/-- **The ping-pong.** -/
theorem pingpong (Γ : Env) (hp : PunctFree Γ) (N : PPNames Γ) :
    ∀ (G : List (Tok × Tok × Tok)) (A B : Name) (x : Tok) (c : Nat),
      (∀ g ∈ G, Group g ∧ A ∉ g.2.2.H ∧ B ∉ g.2.2.H) →
      Γ.find A = some (.fn 0 true [tk N.th, tk N.d1, tk "(", tk ")", tk B]) →
      Γ.find B = some (.fn 0 true [tk N.th, tk N.d1, tk "(", tk ")", tk A]) →
      (∀ y ∈ [N.th, N.d1, N.d0, N.out, "(", ")"], y ≠ A ∧ y ≠ B) → A ≠ B →
      x.s = A → PPInv N A B x.H →
      ∃ Nf o st c', scan Γ Nf c (x :: groupToks G) = some (o, st, c') ∧
        o.map (·.s) = (List.replicate G.length [N.th, N.d0, "(", ")"]).flatten ++ [if G.length % 2 = 0 then A else B] ∧
        ∀ t ∈ o, t.s ∉ t.H
  | [], A, B, x, c, _, hA, _, _, hAB, hx, hinv => by
    refine ⟨2, [x], [], c, ?_, by simp [hx], ?_⟩
    · exact scan_fn_last Γ (by rw [hx]; exact hA) 0 c
    · intro t ht; simp at ht; subst ht
      intro hm; rw [hx] at hm
      rcases hinv A hm with e | e
      · exact hAB e
      · exact e.1 rfl
  | (l, t, r) :: G, A, B, x, c, hG, hA, hB, hd, hAB, hx, hinv => by
    obtain ⟨⟨hl, ht, hr⟩, hAr, hBr⟩ := hG (l, t, r) (by simp)
    have hd' : ∀ y ∈ [N.th, N.d1, N.d0, N.out, "(", ")"], y ≠ B ∧ y ≠ A := fun y hy => (hd y hy).symm
    let K1 := A :: inter x.H r.H
    let K2 := N.d1 :: inter (markOne c K1 { s := N.d1 }).H (markOne c K1 { s := ")" }).H
    -- what K1 and K2 hold
    have mK1 : ∀ n ∈ K1, n = A ∨ (n ≠ A ∧ n ≠ B ∧ n ≠ N.th ∧ n ≠ N.d1 ∧ n ≠ N.d0 ∧ n ≠ N.out ∧ n ≠ "(" ∧ n ≠ ")") := by
      intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · left; rfl
      · obtain ⟨h1, h2⟩ := mem_inter.mp hn
        rcases hinv n h1 with rfl | e
        · exact absurd h2 hBr
        · right; exact e
    have mK2 : ∀ n ∈ K2, n = N.d1 ∨ n ∈ K1 := by
      intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · left; rfl
      · right; exact mem_markOne_body.mp (mem_inter.mp hn).1
    have nK1 : ∀ y ∈ [N.th, N.d1, N.d0, N.out, "(", ")"], y ∉ K1 := by
      intro y hy hm
      rcases mK1 y hm with e | e
      · exact (hd y hy).1 e
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
        · exact e.2.2.1 rfl
        · exact e.2.2.2.1 rfl
        · exact e.2.2.2.2.1 rfl
        · exact e.2.2.2.2.2.1 rfl
        · exact e.2.2.2.2.2.2.1 rfl
        · exact e.2.2.2.2.2.2.2 rfl
    -- the rest, from `GB` on
    have hinv' : PPInv N B A (markOne c K1 { s := B }).H := by
      intro n hn
      rcases mK1 n (mem_markOne_body.mp hn) with e | e
      · left; exact e
      · right; exact ⟨e.2.1, e.1, e.2.2⟩
    obtain ⟨Nf, o, st, c', e, ho, hfin⟩ := pingpong Γ hp N G B A (markOne c K1 { s := B }) (c + 3)
      (fun g hg => let h := hG g (by simp [hg]); ⟨h.1, h.2.2, h.2.1⟩) hB hA hd' (Ne.symm hAB) rfl hinv'
    let rest := groupToks G
    -- `( )` from `D1`, emitted
    have s1 := scan_nameFree_prefix Γ [markOne (c + 1) K2 { s := "(" }, markOne (c + 1) K2 { s := ")" }]
      (by
        intro y hy; simp [markOne] at hy
        rcases hy with rfl | rfl
        · exact hp.1
        · exact hp.2.1) e
    -- `OUT`, empty
    have s2 := scan_obj_step Γ (Nf + 2) (c + 2) (markOne (c + 1) K2 { s := N.out })
      (markOne (c + 1) K2 { s := "(" } :: markOne (c + 1) K2 { s := ")" } :: markOne c K1 { s := B } :: rest) (by
          intro hm
          rcases mK2 _ (mem_markOne_body.mp hm) with e' | e'
          · exact N.out_d1 e'
          · exact nK1 N.out (by simp) e') N.hout ([], [], c + 3) []
      (markOne (c + 1) K2 { s := "(" } :: markOne (c + 1) K2 { s := ")" } :: o, st, c')
      (by simp [subst, substFrom]) (by simp [paste, paste.go]) (by simpa [mark] using s1)
    -- `D0`, emitted (`OUT` follows)
    have s3 := scan_emit_fn Γ (x := markOne (c + 1) K2 { s := N.d0 }) N.hd0 N.out_lp s2
    -- `D1 ( )`
    obtain ⟨st4, s4⟩ := call_toks Γ (x := markOne c K1 { s := N.d1 }) (lp := markOne c K1 { s := "(" })
      (rp := markOne c K1 { s := ")" }) (l := [N.d0, N.out, "(", ")"]) N.hd1
      (by intro hm; exact nK1 N.d1 (by simp) (mem_markOne_body.mp hm)) rfl
      (closeAt_empty rfl (markOne c K1 { s := B } :: rest)) bind_00 (n := Nf + 4) (c := c + 1)
      (by rw [mark_strs]; exact s3)
    -- `TH`, emitted (`D1` follows)
    have s5 := scan_emit_fn Γ (x := markOne c K1 { s := N.th }) N.hth N.d1_lp (by simpa using s4)
    -- `GA ( ~ )`
    have ht1 : t.s ≠ ")" := by rw [ht]; decide
    have ht2 : t.s ≠ "(" := by rw [ht]; decide
    have ht3 : t.s ≠ "," := by rw [ht]; decide
    have hxA : x.s ∉ x.H := by
      intro hm; rw [hx] at hm
      rcases hinv A hm with e' | e'
      · exact hAB e'
      · exact e'.1 rfl
    obtain ⟨st6, s6⟩ := call_toks Γ (x := x) (lp := l) (rp := r) (l := [N.th, N.d1, "(", ")", B])
      (by rw [hx]; exact hA) hxA hl (closeAt_tilde ht1 ht2 hr rest) (bind_va0 ht3) (n := Nf + 6) (c := c)
      (by rw [mark_strs]; rw [hx]; exact s5)
    refine ⟨Nf + 6 + 1, _, st6, c', s6, ?_, ?_⟩
    · simp only [List.map_cons, markOne_s, ho, List.length_cons, List.replicate_succ, List.flatten_cons]
      rw [if_parity]; simp
    · intro u hu
      simp only [List.mem_cons] at hu
      rcases hu with rfl | rfl | rfl | rfl | hu
      · intro hm; exact nK1 N.th (by simp) (mem_markOne_body.mp hm)
      · intro hm
        rcases mK2 _ (mem_markOne_body.mp hm) with e' | e'
        · exact N.d0_d1 e'
        · exact nK1 N.d0 (by simp) e'
      · intro hm
        rcases mK2 _ (mem_markOne_body.mp hm) with e' | e'
        · exact N.d1_lp e'.symm
        · exact nK1 "(" (by simp) e'
      · intro hm
        rcases mK2 _ (mem_markOne_body.mp hm) with e' | e'
        · exact N.d1_rp e'.symm
        · exact nK1 ")" (by simp) e'
      · exact hfin u hu

end PP

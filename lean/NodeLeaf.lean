/-
  Theorem 10, the node lemma for zero, successor and projections.
-/
import NodeCall

namespace PP

theorem all2_single {R : Nat → List Tok → Prop} {j : Nat} {outs : List (List Tok)} (h : All2 R [j] outs) :
    ∃ o, outs = [o] ∧ R j o := by
  cases h with
  | cons hr hrest => cases hrest; exact ⟨_, rfl, hr⟩

theorem find_self {Γ : Env} {t : Term} {π : List Code} (h : Realizes Γ t π) {d : Def}
    (hd : (fullName π .self, d) ∈ t.denvP π) : Γ.find (fullName π .self) = some d := h _ hd

/-- A numeral, marked and rescanned, is emitted as it is. -/
theorem rescan_num {Γ : Env} (hp : PunctFree Γ) {R : List Tok} {v : Nat} (h : IsNum R v) (c : Nat) (N : Nat) :
    ∃ n, N ≤ n ∧ scan Γ n c R = some (R, [], c) :=
  ⟨max N (R.length + 1), Nat.le_max_left _ _,
    scanMono Γ _ c R _ (scan_nameFree' (nameFree_num hp h) c) _ (Nat.le_max_right _ _)⟩

theorem node_succ (Γ : Env) (hp : PunctFree Γ) (π : List Code) (hR : Realizes Γ .succ π) : NodeOK Γ .succ π := by
  intro x lp sep rp as vs hx hid hlp hsep hrp hk hargs _ c
  have hf : Γ.find x.s = some (.fn 1 false [prm 0, tk "(", tk "~", tk ")"]) := by
    rw [hx]; exact find_self hR (by simp [Term.denvP])
  obtain ⟨N, outs, c1, hos, hcall⟩ := call_plain Γ hf hid hlp hsep hrp hk (Or.inl (by decide)) hargs
    (by intro b hb; simp [prm, tk] at hb; rcases hb with rfl | rfl | rfl | rfl <;> simp) c
  obtain ⟨o, rfl, ho, _⟩ := all2_single (by simpa [paramIdx, prm, tk] using hos)
  let R := mark c (x.s :: inter x.H rp.H) (o ++ [{ s := "(" }, { s := "~" }, { s := ")" }])
  have hRn : IsNum R (vs.getD 0 0 + 1) := by
    apply isNum_mark
    unfold IsNum at ho ⊢; simp [ho, unaryList_succ']
  obtain ⟨n, hn, hs⟩ := rescan_num hp hRn c1 N
  have e : toks (plainOut [prm 0, tk "(", tk "~", tk ")"] [o]) = o ++ [{ s := "(" }, { s := "~" }, { s := ")" }] := by
    simp only [prm, tk, plainOut]; rw [toks_map_t]; rfl
  obtain ⟨st', h⟩ := hcall n hn _ (by rw [e]; exact hs)
  refine ⟨n + 1, R, st', c1, h, ?_⟩
  have : Term.eval .succ vs = vs.getD 0 0 + 1 := by cases vs <;> simp [Term.eval]
  rw [this]; exact hRn

theorem node_proj (Γ : Env) (hp : PunctFree Γ) (π : List Code) (k i : Nat) (hik : i < k) (hR : Realizes Γ (.proj k i) π) :
    NodeOK Γ (.proj k i) π := by
  intro x lp sep rp as vs hx hid hlp hsep hrp hk hargs _ c
  have hf : Γ.find x.s = some (.fn k false [prm i]) := by
    rw [hx]; exact find_self hR (by simp [Term.denvP])
  obtain ⟨N, outs, c1, hos, hcall⟩ := call_plain Γ hf hid hlp hsep hrp hk (Or.inl (by omega)) hargs
    (by intro b hb; simp [prm] at hb; subst hb; simp) c
  obtain ⟨o, rfl, ho, _⟩ := all2_single (by simpa [paramIdx, prm] using hos)
  let R := mark c (x.s :: inter x.H rp.H) o
  have hRn : IsNum R (vs.getD i 0) := isNum_mark ho _ _
  obtain ⟨n, hn, hs⟩ := rescan_num hp hRn c1 N
  have e : toks (plainOut [prm i] [o]) = o := by
    simp only [prm, plainOut]; rw [toks_map_t]; simp [toks]
  obtain ⟨st', h⟩ := hcall n hn _ (by rw [e]; exact hs)
  refine ⟨n + 1, R, st', c1, h, ?_⟩
  have : Term.eval (.proj k i) vs = vs.getD i 0 := by simp [Term.eval]
  rw [this]; exact hRn

theorem node_zero (Γ : Env) (π : List Code) (k : Nat) (hR : Realizes Γ (.zero k) π) : NodeOK Γ (.zero k) π := by
  intro x lp sep rp as vs hx hid hlp hsep hrp hk hargs _ c
  have hf : Γ.find x.s = some (.fn 0 true []) := by
    rw [hx]; exact find_self hR (by simp [Term.denvP])
  have hc := closeAt_args sep rp hsep hrp as [] [] (argShape_of_ok hargs)
  simp only [List.reverse_nil, List.nil_append] at hc
  have hb : bind 0 true (joinArgs sep as) = some ([], joinArgs sep as) := by simp [bind, afterCommas]
  have hr : subst Γ 1 (c + 1) [] [] (joinArgs sep as) = some ([], [], c + 1) := by simp [subst, substFrom]
  have hq : scan Γ 1 (c + 1) (mark c (x.s :: inter x.H rp.H) [] ++ []) = some ([], [], c + 1) := by simp [mark, scan]
  have := scan_fn_step Γ 1 c x lp rp (joinArgs sep as) ([] : List Tok) hid hf hlp hc [] _ _ [] _ hb hr (by simp [paste, paste.go]) hq
  refine ⟨2, [], _, _, this, ?_⟩
  have : Term.eval (.zero k) vs = 0 := by simp [Term.eval]
  rw [this]; rfl

end PP

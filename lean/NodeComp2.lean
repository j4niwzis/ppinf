/-
  Theorem 10, the node lemma for compositions.
-/
import NodeComp

namespace PP

theorem all2_map_fst {α β : Type} {R S : α → β → Prop} {f : α → α} (hf : ∀ a b, R a b → S (f a) b) :
    ∀ {l1 : List α} {l2 : List β}, All2 R l1 l2 → All2 S (l1.map f) l2
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hr => .cons (hf _ _ h) (all2_map_fst hf hr)

/-- The value-argument relation a call's substitution gives. -/
abbrev NumArg (vs : List Nat) (j : Nat) (o : List Tok) : Prop := IsNum o (vs.getD j 0) ∧ Fin o

/-- The inner calls `gⱼ(ā)` of a composition, marked: arguments of `h`, with the values `gⱼ(v̄)`. -/
theorem comp_args (Γ : Env) (hp : PunctFree Γ) (π : List Code) (k : Nat) (gs : List Term) (vs : List Nat)
    (hvs : vs.length = k) (c : Nat) (K : List Name)
    (hK1 : ∀ j, fullName (π ++ [.k j]) .self ∉ K) (hK2 : ∀ j, ∀ n ∈ K, Safe (π ++ [.k j]) n)
    (IHg : ∀ j g, gs[j]? = some g → NodeOK Γ g (π ++ [.k j])) (hga : ∀ g ∈ gs, g.arity = k) :
    ∀ (L : List (Term × Nat)) (chunks : List (List (List Tok))), (∀ p ∈ L, gs[p.2]? = some p.1) →
      All2 (All2 (NumArg vs)) (L.map fun _ => List.range k) chunks →
      ArgsOK Γ (List.zipWith (fun p ch => mark c K (toks (plainOut (callB π k p.2) ch))) L chunks) (L.map fun p => p.1.eval vs)
  | [], [], _, _ => .nil
  | (g, j) :: L, ch :: chunks, hL, .cons hch hrest => by
    have hg : gs[j]? = some g := hL (g, j) (by simp)
    have hgk : g.arity = k := hga g (List.mem_of_getElem? hg)
    have hlen : ch.length = k := by simpa using all2_length hch
    have hnums : All2 (fun A v => IsNum A v) (ch.map (mark c K)) vs :=
      all2_map_fst (R := fun o v => IsNum o v ∧ Fin o) (fun o v h => isNum_mark h.1 c K)
        (all2_range hvs (P := fun o v => IsNum o v ∧ Fin o) hch)
    have e : mark c K (toks (plainOut (callB π k j) ch)) =
        callToks (markOne c K { s := fullName (π ++ [.k j]) .self }) (markOne c K { s := "(" }) (markOne c K comma)
          (markOne c K { s := ")" }) (ch.map (mark c K)) := by
      rw [toks_callB π k j ch hlen, mark_callToks]
    refine .cons ⟨?_, ?_⟩ (comp_args Γ hp π k gs vs hvs c K hK1 hK2 IHg hga L chunks
      (fun p hp' => hL p (by simp [hp'])) hrest)
    · show ArgShape (mark c K (toks (plainOut (callB π k j) ch))); rw [e]
      refine argShape_call (fullName_ne_rp _ _) (fullName_ne_lp _ _) (fullName_ne_comma _ _) rfl rfl rfl _ ?_
      intro A hA
      obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hA
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ho
      have := (all2_iff.mp hch).2 i (by simp; omega) hi
      exact ⟨_, isNum_mark this.1 c K⟩
    · show Expands Γ (mark c K (toks (plainOut (callB π k j) ch))) (g.eval vs); rw [e]
      refine expands_of_scan fun c' => IHg j g hg _ _ _ _ _ vs rfl ?_ rfl rfl rfl (by simp [hlen, hgk]) ?_ ?_ c'
      · intro h; exact hK1 j (mem_markOne_body.mp h)
      · exact argsOK_nums hp (by simpa using hnums)
      · intro n hn
        exact hK2 j n (mem_markOne_body.mp (mem_inter.mp hn).1)

theorem range_zipIdx {α β : Type} (l : List α) (f : Nat → β) : (List.range l.length).map f = l.zipIdx.map fun p => f p.2 := by
  apply List.ext_getElem <;> simp

theorem zipIdx_get {α : Type} (l : List α) : ∀ p ∈ l.zipIdx, l[p.2]? = some p.1 := by
  intro p hp; exact List.mem_zipIdx_iff_getElem?.mp hp

theorem eval_comp (k : Nat) (h : Term) (gs : List Term) (vs : List Nat) :
    (Term.comp k h gs).eval vs = h.eval (gs.map fun g => g.eval vs) := by
  simp [Term.eval]

theorem flatten_length_all2 : ∀ (bs : List (List BTok)) (chunks : List (List (List Tok))),
    All2 (fun b ch => ch.length = (paramIdx b).length) bs chunks → chunks.flatten.length = (bs.map paramIdx).flatten.length
  | [], [], .nil => rfl
  | _ :: bs, _ :: chunks, .cons h hr => by simp [h, flatten_length_all2 bs chunks hr]

/-- **Compositions.** -/
theorem node_comp (Γ : Env) (hp : PunctFree Γ) (π : List Code) (k : Nat) (h : Term) (gs : List Term)
    (hR : Realizes Γ (.comp k h gs) π) (hha : h.arity = gs.length) (hga : ∀ g ∈ gs, g.arity = k)
    (IHh : NodeOK Γ h (π ++ [.h])) (IHg : ∀ j g, gs[j]? = some g → NodeOK Γ g (π ++ [.k j])) :
    NodeOK Γ (.comp k h gs) π := by
  intro x lp sep rp as vs hx hid hlp hsep hrp hk hargs hdis c
  have hvs : vs.length = k := by rw [← argsOK_length hargs]; exact hk
  let calls := (List.range gs.length).map fun j => [nm (π ++ [.k j]) .self, tk "("] ++ joinB ((prms k).map ([·])) ++ [tk ")"]
  have hcallsB : calls = (List.range gs.length).map (callB π k) := rfl
  let body : List BTok := [nm (π ++ [.h]) .self, tk "("] ++ joinB calls ++ [tk ")"]
  have hf : Γ.find x.s = some (.fn k false body) := by
    rw [hx]; exact find_self hR (by unfold Term.denvP; exact List.mem_cons_self ..)
  have hplain : Plain body := by
    refine plain_append (plain_append ?_ (plain_joinB _ ?_)) (plain_single _ (by simp [tk]))
    · intro y hy; simp [nm, tk] at hy; rcases hy with rfl | rfl <;> simp
    · intro b hb; rw [hcallsB] at hb; obtain ⟨j, _, rfl⟩ := List.mem_map.mp hb; exact plain_callB π k j
  have hne : k ≠ 0 ∨ as = [] := by
    by_cases hk0 : k = 0
    · right; apply List.eq_nil_of_length_eq_zero; simp [Term.arity] at hk; omega
    · left; exact hk0
  obtain ⟨N, outs, c1, hos, hcall⟩ := call_plain Γ hf hid hlp hsep hrp (by simpa [Term.arity] using hk) hne hargs hplain c
  -- the outputs, call by call
  have hpi : paramIdx body = (calls.map paramIdx).flatten := by
    simp [body, paramIdx_append, paramIdx_joinB, nm, tk, paramIdx]
  rw [hpi] at hos
  obtain ⟨chunks, rfl, hch⟩ := all2_flatten hos
  have hcalls : calls = gs.zipIdx.map fun p => callB π k p.2 := by rw [hcallsB]; exact range_zipIdx gs (callB π k)
  have hch' : All2 (All2 (NumArg vs)) (gs.zipIdx.map fun _ => List.range k) chunks := by
    have : calls.map paramIdx = gs.zipIdx.map fun _ => List.range k := by
      rw [hcalls]; simp [Function.comp_def, paramIdx_callB]
    rw [← this]; exact hch
  have hlens : All2 (fun b ch => ch.length = (paramIdx b).length) calls chunks :=
    all2_map_left (f := paramIdx) (R := fun l ch => All2 (NumArg vs) l ch) (fun b ch h' => all2_length h') hch
  -- the replacement: `h ( g₀ ( ā ) , … )`
  have htoks : toks (plainOut body chunks.flatten) = callToks { s := fullName (π ++ [.h]) .self } { s := "(" } comma
      { s := ")" } (List.zipWith (fun b ch => toks (plainOut b ch)) calls chunks) := by
    rw [show chunks.flatten = ([] ++ chunks.flatten) ++ [] by simp]
    rw [plainOut_append _ _ ([] ++ chunks.flatten) [] (by
        rw [paramIdx_append, paramIdx_joinB, List.nil_append, flatten_length_all2 calls chunks hlens]; simp [nm, tk, paramIdx]),
      plainOut_append _ _ [] _ (by simp [nm, tk, paramIdx])]
    rw [toks_append, toks_append, toks_joinB calls chunks hlens]
    simp [nm, tk, plainOut, toks, tokOf, callToks]
  -- `h` on the marked inner calls
  let K := x.s :: inter x.H rp.H
  let As := List.zipWith (fun p ch => mark c K (toks (plainOut (callB π k p.2) ch))) gs.zipIdx chunks
  have hAs : (List.zipWith (fun b ch => toks (plainOut b ch)) calls chunks).map (mark c K) = As := by
    rw [hcalls, List.zipWith_map_left, List.map_zipWith]
  have hargs' : ArgsOK Γ As (gs.map fun g => g.eval vs) := by
    have := comp_args Γ hp π k gs vs hvs c K (fun j => child_free (.k j) hx hdis) (fun j => child_ctx (.k j) hx hdis)
      IHg hga gs.zipIdx chunks (zipIdx_get gs) hch'
    have e : gs.zipIdx.map (fun p => p.1.eval vs) = gs.map fun g => g.eval vs := by
      apply List.ext_getElem <;> simp
    rwa [e] at this
  have hlenA : As.length = h.arity := by
    have := all2_length hch'
    simp [As, hha, this]
  obtain ⟨N2, o, st, c2, e2, ho⟩ := IHh (markOne c K { s := fullName (π ++ [.h]) .self }) (markOne c K { s := "(" })
    (markOne c K comma) (markOne c K { s := ")" }) As (gs.map fun g => g.eval vs) rfl
    (fun hm => child_free .h hx hdis (mem_markOne_body.mp hm)) rfl rfl rfl hlenA hargs'
    (fun n hn => child_ctx .h hx hdis n (mem_markOne_body.mp (mem_inter.mp hn).1)) c1
  have e2' := scanMono Γ N2 c1 _ _ e2 (max N N2) (Nat.le_max_right _ _)
  obtain ⟨st', hfin⟩ := hcall (max N N2) (Nat.le_max_left _ _) (o, st, c2) (by
    rw [htoks, mark_callToks, hAs]; exact e2')
  exact ⟨max N N2 + 1, o, st', c2, hfin, by rw [eval_comp]; exact ho⟩

end PP

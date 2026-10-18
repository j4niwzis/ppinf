/-
  Theorem 10, the node lemma for compositions: `p(ā) → h(g₀(ā), …)`, each `gⱼ(ā)` expanded
  alone (its node lemma), then `h` on their values (its node lemma).
-/
import CompShape

namespace PP

/-! Depths, on spellings. -/

def walkS : Nat → List String → Option Nat
  | d, [] => some d
  | d, s :: r =>
    if s == ")" then (if d == 0 then none else walkS (d - 1) r)
    else if s == "(" then walkS (d + 1) r
    else if s == "," && d == 0 then none
    else walkS d r

theorem walk_spell : ∀ (d : Nat) (xs : List Tok), walk d xs = walkS d (xs.map (·.s))
  | d, [] => rfl
  | d, x :: r => by
    simp only [walk, walkS, List.map_cons]
    split <;> (try split) <;> (try split) <;> simp_all [walk_spell]

theorem walkS_append : ∀ (a b : List String) (d : Nat), walkS d (a ++ b) = (walkS d a).bind fun d' => walkS d' b
  | [], b, d => rfl
  | s :: a, b, d => by
    simp only [List.cons_append, walkS]
    split <;> (try split) <;> (try split) <;> simp_all [walkS_append]

theorem walkS_num : ∀ (v d : Nat), walkS d (unaryList v) = some d
  | 0, d => rfl
  | v + 1, d => by
    rw [show unaryList (v + 1) = ["(", "~", ")"] ++ unaryList v from rfl, walkS_append]
    simp [walkS, walkS_num v d]

theorem walk_num {o : List Tok} {v : Nat} (h : IsNum o v) (d : Nat) : walk d o = some d := by
  rw [walk_spell, h, walkS_num]

theorem walk_append (a b : List Tok) (d : Nat) : walk d (a ++ b) = (walk d a).bind fun d' => walk d' b := by
  rw [walk_spell, walk_spell, List.map_append, walkS_append]
  congr 1; funext d'; rw [walk_spell]

theorem walk_joinArgs (sep : Tok) (hsep : sep.s = ",") (d : Nat) (hd : d ≠ 0) :
    ∀ (as : List (List Tok)), (∀ A ∈ as, walk d A = some d) → walk d (joinArgs sep as) = some d
  | [], _ => rfl
  | [A], h => by simpa [joinArgs] using h A (by simp)
  | A :: B :: as, h => by
    rw [joinArgs_cons_cons, walk_append, h A (by simp)]
    simp only [Option.bind_some]
    have : walk d (sep :: joinArgs sep (B :: as)) = walk d (joinArgs sep (B :: as)) := by
      simp only [walk, hsep]
      have hd' : (d == 0) = false := by simpa using hd
      simp [hd']
    rw [this]; exact walk_joinArgs sep hsep d hd (B :: as) (fun X hX => h X (by simp_all))

/-- A call on numerals is an argument. -/
theorem argShape_call {x lp sep rp : Tok} (hx1 : x.s ≠ ")") (hx2 : x.s ≠ "(") (hx3 : x.s ≠ ",") (hlp : lp.s = "(")
    (hsep : sep.s = ",") (hrp : rp.s = ")") (as : List (List Tok)) (h : ∀ A ∈ as, ∃ v, IsNum A v) :
    ArgShape (callToks x lp sep rp as) := by
  unfold ArgShape callToks
  have hx1' : (x.s == ")") = false := by simpa using hx1
  have hx2' : (x.s == "(") = false := by simpa using hx2
  have hx3' : (x.s == ",") = false := by simpa using hx3
  simp only [walk, hx1', hx2', hx3', hlp, Bool.false_eq_true, ite_false, Bool.false_and, beq_self_eq_true, ite_true]
  rw [walk_append, walk_joinArgs sep hsep 1 (by decide) as (fun A hA => by obtain ⟨v, hv⟩ := h A hA; exact walk_num hv 1)]
  simp [walk, hrp]

/-! Expansions. -/

theorem isNum_finalize' {o : List Tok} {v : Nat} (h : IsNum o v) : IsNum (finalize o) v := by
  unfold IsNum at *; simp [finalize, Function.comp_def, h]

theorem expands_of_scan {Γ : Env} {A : List Tok} {v : Nat}
    (h : ∀ c, ∃ N o st c', scan Γ N c A = some (o, st, c') ∧ IsNum o v) : Expands Γ A v := by
  intro c
  obtain ⟨N, o, st, c', e, ho⟩ := h c
  exact ⟨N, finalize o, st, c', by simp [expand, e], isNum_finalize' ho⟩

theorem expands_num {Γ : Env} (hp : PunctFree Γ) {A : List Tok} {v : Nat} (h : IsNum A v) : Expands Γ A v :=
  expands_of_scan fun c => ⟨_, A, [], c, scan_nameFree' (nameFree_num hp h) c, h⟩

theorem argsOK_nums {Γ : Env} (hp : PunctFree Γ) : ∀ {as : List (List Tok)} {vs : List Nat},
    All2 (fun A v => IsNum A v) as vs → ArgsOK Γ as vs
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hr => .cons ⟨by unfold ArgShape; exact walk_num h 0, expands_num hp h⟩ (argsOK_nums hp hr)

/-! Marks and names. -/

theorem mem_union {n : Name} {K H : List Name} : n ∈ union K H ↔ n ∈ K ∨ n ∈ H := by
  unfold union; simp only [List.mem_append, List.mem_filter, decide_eq_true_eq]
  by_cases h : n ∈ K <;> simp [h]

theorem mem_inter {n : Name} {H J : List Name} : n ∈ inter H J ↔ n ∈ H ∧ n ∈ J := by
  unfold inter; simp

theorem markOne_s (c : Nat) (K : List Name) (x : Tok) : (markOne c K x).s = x.s := rfl

theorem mem_markOne_body {c : Nat} {K : List Name} {s : String} {n : Name} : n ∈ (markOne c K { s }).H ↔ n ∈ K := by
  simp [markOne, mem_union]

theorem isNum_markAll {o : List Tok} {v : Nat} (h : IsNum o v) (c : Nat) (K : List Name) : IsNum (o.map (markOne c K)) v := by
  unfold IsNum at *; simp [Function.comp_def, markOne_s, h]

theorem below_child (π : List Code) (c : Code) : Below π (fullName (π ++ [c]) .self) := ⟨[c], .self, by simp⟩

theorem below_mono {π : List Code} {c : Code} {n : Name} (h : Below (π ++ [c]) n) : Below π n := by
  obtain ⟨q, x, rfl⟩ := h; exact ⟨c :: q, x, by simp⟩

theorem not_below_parent (π : List Code) (c : Code) (x : Helper) : ¬ Below (π ++ [c]) (fullName π x) := by
  rintro ⟨q, y, h⟩
  have := (fullName_inj h).1
  have := congrArg List.length this; simp at this

/-- The context of a child: the parent's mark hides neither the child nor anything below it. -/
theorem child_ctx {π : List Code} (c : Code) {x rp : Tok} (hx : x.s = fullName π .self)
    (hdis : ∀ n ∈ inter x.H rp.H, Safe π n) : ∀ n ∈ x.s :: inter x.H rp.H, Safe (π ++ [c]) n := by
  intro n hn
  rcases List.mem_cons.mp hn with rfl | hn
  · rw [hx]; exact ⟨not_below_parent π c .self, π, .self, rfl⟩
  · exact ⟨fun hb => (hdis n hn).1 (below_mono hb), (hdis n hn).2⟩

theorem child_free {π : List Code} (c : Code) {x rp : Tok} (hx : x.s = fullName π .self)
    (hdis : ∀ n ∈ inter x.H rp.H, Safe π n) : fullName (π ++ [c]) .self ∉ x.s :: inter x.H rp.H := by
  intro h
  rcases List.mem_cons.mp h with h | h
  · rw [hx] at h
    have := (fullName_inj h).1; have := congrArg List.length this; simp at this
  · exact (hdis _ h).1 (below_child π c)

/-! Plain bodies. -/

theorem plain_append {a b : List BTok} (ha : Plain a) (hb : Plain b) : Plain (a ++ b) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact ha x h
  · exact hb x h

theorem plain_tk (l : List String) : Plain (l.map tk) := by
  intro x hx; obtain ⟨s, _, rfl⟩ := List.mem_map.mp hx; simp [tk]

theorem plain_single (b : BTok) (h : b ≠ .paste ∧ b ≠ .va) : Plain [b] := by
  intro x hx; simp at hx; subst hx; exact h

theorem plain_joinB : ∀ (bs : List (List BTok)), (∀ b ∈ bs, Plain b) → Plain (joinB bs)
  | [], _ => by intro x hx; simp [joinB] at hx
  | [b], h => by simpa [joinB] using h b (by simp)
  | a :: b :: bs, h => by
    rw [joinB_cons_cons]
    exact plain_append (h a (by simp)) (plain_append (plain_single _ (by simp [tk]))
      (plain_joinB (b :: bs) (fun x hx => h x (by simp_all))))

/-- A composition's call of its `j`-th inner function. -/
def callB (π : List Code) (k j : Nat) : List BTok :=
  [nm (π ++ [.k j]) .self, tk "("] ++ joinB ((prms k).map ([·])) ++ [tk ")"]

theorem prms_single (k : Nat) : (prms k).map ([·]) = (List.range k).map fun i => [prm i] := by
  simp [prms, Function.comp_def]

theorem plain_callB (π : List Code) (k j : Nat) : Plain (callB π k j) := by
  unfold callB
  refine plain_append (plain_append ?_ ?_) (plain_single _ (by simp [tk]))
  · intro x hx; simp [nm, tk] at hx; rcases hx with rfl | rfl <;> simp
  · rw [prms_single]; exact plain_joinB _ (fun b hb => by
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb; exact plain_single _ (by simp [prm]))

theorem paramIdx_callB (π : List Code) (k j : Nat) : paramIdx (callB π k j) = List.range k := by
  unfold callB
  rw [paramIdx_append, paramIdx_append, prms_single, paramIdx_joinB_single]
  simp [nm, tk, paramIdx]

theorem toks_callB (π : List Code) (k j : Nat) (ch : List (List Tok)) (hch : ch.length = k) :
    toks (plainOut (callB π k j) ch) = callToks { s := fullName (π ++ [.k j]) .self } { s := "(" } comma { s := ")" } ch := by
  unfold callB
  rw [show ch = ([] ++ ch) ++ [] by simp]
  rw [plainOut_append _ _ ([] ++ ch) [] (by
      rw [paramIdx_append, prms_single, paramIdx_joinB_single]; simp [nm, tk, paramIdx, hch]),
    plainOut_append _ _ [] ch (by simp [nm, tk, paramIdx])]
  rw [toks_append, toks_append, prms_single, toks_joinB_single _ _ (by simp [hch])]
  simp [nm, tk, plainOut, toks, tokOf, callToks]

/-! Lists by index. -/

theorem all2_iff {α β : Type} {R : α → β → Prop} : ∀ {l1 : List α} {l2 : List β},
    All2 R l1 l2 ↔ l1.length = l2.length ∧ ∀ i (h1 : i < l1.length) (h2 : i < l2.length), R l1[i] l2[i]
  | [], [] => ⟨fun _ => ⟨rfl, fun i h => by simp at h⟩, fun _ => .nil⟩
  | [], _ :: _ => ⟨fun h => (by cases h), fun h => (by simp at h)⟩
  | _ :: _, [] => ⟨fun h => (by cases h), fun h => (by simp at h)⟩
  | a :: l1, b :: l2 => by
    constructor
    · intro h
      cases h with
      | cons hr hrest =>
        obtain ⟨hl, hi⟩ := all2_iff.mp hrest
        refine ⟨by simp [hl], fun i h1 h2 => ?_⟩
        cases i with
        | zero => exact hr
        | succ i => exact hi i (by simpa using h1) (by simpa using h2)
    · rintro ⟨hl, hi⟩
      exact .cons (hi 0 (by simp) (by simp)) (all2_iff.mpr ⟨by simpa using hl, fun i h1 h2 =>
        hi (i + 1) (by simpa using h1) (by simpa using h2)⟩)

theorem all2_range {P : List Tok → Nat → Prop} {k : Nat} {ch : List (List Tok)} {vs : List Nat} (hvs : vs.length = k)
    (h : All2 (fun i o => P o (vs.getD i 0)) (List.range k) ch) : All2 P ch vs := by
  obtain ⟨hl, hi⟩ := all2_iff.mp h
  refine all2_iff.mpr ⟨by simp at hl; omega, fun i h1 h2 => ?_⟩
  have := hi i (by simp; omega) h1
  simp only [List.getElem_range] at this
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some] at this

theorem all2_map {α β : Type} {R : α → β → Prop} {f : β → β} {S : α → β → Prop} (hf : ∀ a b, R a b → S a (f b)) :
    ∀ {l1 : List α} {l2 : List β}, All2 R l1 l2 → All2 S l1 (l2.map f)
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hr => .cons (hf _ _ h) (all2_map hf hr)

theorem all2_map_left {α β γ : Type} {R : α → γ → Prop} {f : β → α} {S : β → γ → Prop} (hf : ∀ a b, R (f a) b → S a b) :
    ∀ {l1 : List β} {l2 : List γ}, All2 R (l1.map f) l2 → All2 S l1 l2
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hr => .cons (hf _ _ h) (all2_map_left hf hr)

/-! Names are not punctuation. -/

theorem fullName_toList (π : List Code) (x : Helper) : (fullName π x).toList = 'T' :: (π.flatMap Code.chars ++ x.suffix.toList) := by
  simp [fullName, nodeName]

theorem fullName_ne {π : List Code} {x : Helper} {s : String} (hs : s.toList.head? ≠ some 'T') : fullName π x ≠ s := by
  intro h; apply hs; rw [← h, fullName_toList]; rfl

theorem fullName_ne_lp (π : List Code) (x : Helper) : fullName π x ≠ "(" := fullName_ne (by decide)
theorem fullName_ne_rp (π : List Code) (x : Helper) : fullName π x ≠ ")" := fullName_ne (by decide)
theorem fullName_ne_comma (π : List Code) (x : Helper) : fullName π x ≠ "," := fullName_ne (by decide)

end PP

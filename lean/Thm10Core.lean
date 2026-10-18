/-
  Theorem 10 (pp_primrec.tex, §5): every primitive recursive function is pp-computable --
  the node lemma for every term by induction, applied to the root call `T(x̄₁, …, x̄ₖ)`.
-/
import NodePrec

namespace PP

/-- pp-computable, for functions on lists of a given length (the core-Lean form). -/
def PpComputableL (k : Nat) (f : List Nat → Nat) : Prop :=
  ∃ (Γ : Env) (F : String), ∀ xs : List Nat, xs.length = k → ∃ fuel,
    run Γ fuel (call F xs) = some (unaryToks (f xs))

/-! The built environment has no macro named like punctuation. -/

theorem find_none {L : Env} {s : String} (h : ∀ e ∈ L, e.1 ≠ s) : L.find s = none := by
  unfold Env.find
  cases hf : L.find? (·.1 == s) with
  | none => rfl
  | some e =>
    have hm := List.mem_of_find?_eq_some hf
    have := List.find?_some hf
    simp at this; exact absurd this (h e hm)

theorem punctFree_denvP (t : Term) : PunctFree (t.denvP []) := by
  have h : ∀ s : String, s.toList.head? ≠ some 'T' → (t.denvP []).find s = none := by
    intro s hs; apply find_none; intro e he hes
    obtain ⟨q, x, e1⟩ := mem_names t [] e he
    exact fullName_ne hs (e1 ▸ hes)
  exact ⟨h "(" (by decide), h ")" (by decide), h "," (by decide), h "~" (by decide), h "_END" (by decide)⟩

/-! The node lemma, for every well-formed term. -/

theorem wfs_mem {k : Nat} : ∀ {gs : List Term}, Term.WFs k gs → ∀ g ∈ gs, g.arity = k ∧ g.WF
  | [], _, g, h => by simp at h
  | g' :: gs, hw, g, h => by
    simp only [Term.WFs] at hw
    obtain ⟨h1, h2, h3⟩ := hw
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨h1, h2⟩
    · exact wfs_mem h3 g h

theorem node_all (Γ : Env) (hp : PunctFree Γ) (t : Term) : ∀ (π : List Code), t.WF → Realizes Γ t π → NodeOK Γ t π :=
  Term.rec (motive_1 := fun t => ∀ π, t.WF → Realizes Γ t π → NodeOK Γ t π)
    (motive_2 := fun gs => ∀ (j : Nat) (g : Term), gs[j]? = some g → ∀ π, g.WF → Realizes Γ g π → NodeOK Γ g π)
    (fun k π _ hR => node_zero Γ π k hR)
    (fun π _ hR => node_succ Γ hp π hR)
    (fun k i π hw hR => node_proj Γ hp π k i (by simpa only [Term.WF] using hw) hR)
    (fun k h gs ih ihs π hw hR => by
      simp only [Term.WF] at hw
      obtain ⟨hha, hwh, hwg⟩ := hw
      have a := ih (π ++ [.h]) hwh (realizes_comp_h hR)
      have b1 := fun (j : Nat) (g : Term) (hg : gs[j]? = some g) => (wfs_mem hwg g (List.mem_of_getElem? hg)).2
      have b2 := fun (j : Nat) (g : Term) (hg : gs[j]? = some g) => realizes_comp_g hR j g hg
      have b := fun (j : Nat) (g : Term) (hg : gs[j]? = some g) => ihs j g hg (π ++ [.k j]) (b1 j g hg) (b2 j g hg)
      have c := node_comp Γ hp π k h gs hR hha (fun g hg => (wfs_mem hwg g hg).1) a b
      exact c)
    (fun f g ihf ihg π hw hR => by
      simp only [Term.WF] at hw
      obtain ⟨hga, hwf, hwg⟩ := hw
      have a := ihf (π ++ [.f]) hwf (realizes_prec_f hR)
      have b := ihg (π ++ [.r]) hwg (realizes_prec_g hR)
      have c := node_prec Γ hp π f g hR hga a b
      exact c)
    (fun j g hg => by simp at hg)
    (fun hd tl ih ihs j g hg => by
      cases j with
      | zero => simp at hg; subst hg; exact ih
      | succ j => exact ihs j g (by simpa using hg))
    t

/-! The root call. -/

theorem tokenize_T : tokenize "T" = ["T"] := by decide

theorem nodeName_root : nodeName [] = "T" := by decide

theorem tokenize_unary' (n : Nat) : tokenize (unary n) = unaryList n := by
  unfold tokenize unary
  rw [String.toList_ofList, ← List.append_nil (unaryChars n), go_unary, go_nil]
  simp [flushOf]

theorem unaryToks_eq (n : Nat) : unaryToks n = unaryList n := by
  unfold unaryToks input; rw [List.map_map]; simp [Function.comp_def, tokenize_unary']

def mkTok (s : String) : Tok := { s }

theorem map_intercalate {α β : Type} (f : α → β) (sep : List α) : ∀ (l : List (List α)),
    (sep.intercalate l).map f = (sep.map f).intercalate (l.map (List.map f))
  | [] => rfl
  | [a] => by simp
  | a :: b :: l => by
    rw [List.intercalate_cons_cons, List.map_append, List.map_append, map_intercalate f sep (b :: l)]
    simp [List.intercalate_cons_cons]

theorem input_root (xs : List Nat) :
    input (call "T" xs) = callToks (mkTok "T") (mkTok "(") comma (mkTok ")") (xs.map fun v => (unaryList v).map mkTok) := by
  rw [input_call, tokenize_T]
  simp only [callToks, argToks, joinArgs, List.map_append, List.map_cons, List.map_nil, map_intercalate, List.map_map]
  simp [mkTok, comma, Function.comp_def]
  rfl

theorem nums_all : ∀ xs : List Nat, All2 (fun A v => IsNum A v) (xs.map fun v => (unaryList v).map mkTok) xs
  | [] => .nil
  | v :: xs => .cons (by unfold IsNum; simp [mkTok, Function.comp_def]) (nums_all xs)

/-- **Theorem 10**, core form: every well-formed PR term computes a pp-computable function. -/
theorem theorem10_core (t : Term) (hw : t.WF) : PpComputableL t.arity t.eval := by
  let Γ := t.denvP []
  have hp := punctFree_denvP t
  refine ⟨Γ, "T", fun xs hxs => ?_⟩
  have hnode := node_all Γ hp t [] hw (realizes_root t)
  have hnums := nums_all xs
  obtain ⟨N, o, st, c', e, ho⟩ := hnode (mkTok "T") (mkTok "(") comma (mkTok ")") _ xs
    (by show "T" = fullName [] .self; unfold fullName; rw [nodeName_root]; rfl) (by intro h; cases h) rfl rfl rfl
    (by rw [List.length_map]; exact hxs) (argsOK_nums hp hnums) (by intro n hn; simp [mkTok, inter] at hn) 1
  refine ⟨N, ?_⟩
  unfold run expand
  rw [input_root, e]
  simp only [Option.map_some, unaryToks_eq]
  rw [finalize_spell]; exact congrArg some ho

end PP

/-
  Theorem 10 (pp_primrec.tex, §5) against Mathlib: every primitive recursive `f : ℕᵏ → ℕ` is
  pp-computable -- through Mathlib's `Nat.Primrec'`, whose constructors are `Term`'s -- and so,
  with Theorem 9, pp-computable is primitive recursive, exactly.
-/
import Thm9
import Thm10Core

namespace PP

theorem wfs_ofFn {k n : Nat} (ts : _root_.Fin n → Term) (h : ∀ i, (ts i).arity = k ∧ (ts i).WF) : Term.WFs k (List.ofFn ts) := by
  induction n with
  | zero => simp [Term.WFs]
  | succ n ih =>
    rw [List.ofFn_succ]
    simp only [Term.WFs]
    exact ⟨(h 0).1, (h 0).2, ih (fun i => ts i.succ) (fun i => h i.succ)⟩

theorem map_ofFn' {n : Nat} (ts : _root_.Fin n → Term) (w : List Nat) :
    (List.ofFn ts).map (fun g => g.eval w) = List.ofFn fun i => (ts i).eval w := by
  simp [List.map_ofFn, Function.comp_def]

/-- **Mathlib's primitive recursive functions are terms.** -/
theorem term_of_primrec' : ∀ {n : Nat} {f : List.Vector ℕ n → ℕ}, Nat.Primrec' f →
    ∃ t : Term, t.WF ∧ t.arity = n ∧ ∀ v : List.Vector ℕ n, t.eval v.toList = f v
  | _, _, .zero => ⟨.zero 0, trivial, rfl, fun v => by simp [Term.eval]⟩
  | _, _, .succ => ⟨.succ, trivial, rfl, fun v => by
      obtain ⟨l, hl⟩ := v
      match l, hl with
      | [a], _ => simp [Term.eval, List.Vector.head]⟩
  | n, _, .get i => ⟨.proj n i, i.2, rfl, fun v => by
      simp [Term.eval, List.getD_eq_getElem?_getD, List.Vector.get_eq_get_toList]⟩
  | m, _, .comp (n := n) (f := f) g hf hg => by
    obtain ⟨tf, hwf, haf, hef⟩ := term_of_primrec' hf
    have hg' := fun i => term_of_primrec' (hg i)
    let ts : _root_.Fin n → Term := fun i => Classical.choose (hg' i)
    have hts : ∀ i, (ts i).WF ∧ (ts i).arity = m ∧ ∀ v, (ts i).eval v.toList = g i v :=
      fun i => Classical.choose_spec (hg' i)
    refine ⟨.comp m tf (List.ofFn ts), ⟨by simp [haf], hwf, wfs_ofFn ts (fun i => ⟨(hts i).2.1, (hts i).1⟩)⟩, rfl,
      fun v => ?_⟩
    rw [eval_comp, map_ofFn']
    have : (List.ofFn fun i => (ts i).eval v.toList) = (List.Vector.ofFn fun i => g i v).toList := by
      simp [(hts _).2.2]
    rw [this, hef]
  | _, _, .prec (n := n) (f := f) (g := g) hf hg => by
    obtain ⟨tf, hwf, haf, hef⟩ := term_of_primrec' hf
    obtain ⟨tg, hwg, hag, heg⟩ := term_of_primrec' hg
    refine ⟨.prec tf tg, ⟨by simp [haf, hag], hwf, hwg⟩, by simp [Term.arity, haf], fun v => ?_⟩
    simp only [Term.eval]
    obtain ⟨l, hl⟩ := v
    match l, hl with
    | a :: ys, hl =>
      simp only [List.Vector.toList_mk, List.tail_cons, List.headD_cons]
      have hys : ys.length = n := by simpa using hl
      have hf' : tf.eval ys = f ⟨ys, hys⟩ := hef ⟨ys, hys⟩
      rw [hf']
      show _ = Nat.rec (motive := fun _ => ℕ) (f ⟨ys, hys⟩) (fun y IH => g (y ::ᵥ IH ::ᵥ ⟨ys, hys⟩)) a
      clear hl
      induction a with
      | zero => rfl
      | succ a ih =>
        simp only
        rw [ih]
        exact heg (_ ::ᵥ _ ::ᵥ ⟨ys, hys⟩)

/-- **Theorem 10**: every primitive recursive `f : ℕᵏ → ℕ` is pp-computable. -/
theorem theorem10 {k : Nat} {f : List.Vector ℕ k → ℕ} (hf : Primrec f) : PpComputable f := by
  obtain ⟨t, hw, ha, he⟩ := term_of_primrec' (Nat.Primrec'.prim_iff.mpr hf)
  obtain ⟨Γ, F, h⟩ := theorem10_core t hw
  refine ⟨Γ, F, fun xs => ?_⟩
  obtain ⟨fuel, e⟩ := h xs.toList (by simp [ha])
  exact ⟨fuel, by rw [e, he]⟩

/-- **The paper's main result**: a function `ℕᵏ → ℕ` is pp-computable exactly when it is
    primitive recursive. -/
theorem ppComputable_iff_primrec {k : Nat} (f : List.Vector ℕ k → ℕ) : PpComputable f ↔ Primrec f :=
  ⟨fun h => theorem9 k f h, theorem10⟩

end PP

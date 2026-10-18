/-
  Theorem 9: pasting is primitive recursive -- `pasted`, `pasteTwo`, `paste` through its fold,
  and `adjacentPaste`.
-/
import PrimScan

open Primrec

namespace PP

variable {α : Type} [Primcodable α]

theorem rtok_t {f : α → Tok} (hf : Primrec f) : Primrec fun a => RTok.t (f a) :=
  ((of_equiv_symm (e := rtokEquiv)).comp (sumInl.comp hf)).of_eq fun _ => rfl
theorem list_isEmpty {β : Type} [Primcodable β] : Primrec (@List.isEmpty β) :=
  (list_casesOn Primrec.id (const true) (const false).to₂).of_eq fun l => by cases l <;> rfl

theorem rtok_const (r : RTok) : Primrec fun _ : α => r := const r

def RTok.isPm : RTok → Bool
  | .pm => true
  | _ => false

theorem isPm_prim : Primrec RTok.isPm :=
  (sumCasesOn (of_equiv (e := rtokEquiv)) (const false).to₂ (snd).to₂).of_eq fun r => by cases r <;> rfl

theorem isOp_prim : Primrec RTok.isOp :=
  (sumCasesOn (of_equiv (e := rtokEquiv)) (const false).to₂ (Primrec.not.comp snd).to₂).of_eq fun r => by cases r <;> rfl

theorem tokOf_prim : Primrec tokOf :=
  (sumCasesOn (of_equiv (e := rtokEquiv)) (option_some.comp snd).to₂ (const none).to₂).of_eq fun r => by cases r <;> rfl

theorem listAll_ident : Primrec fun l : List Char => l.all identChar :=
  ((PrimrecPred.forall_mem_list (p := fun c => identChar c = true)
    (Primrec.primrecPred (p := fun c => identChar c = true) (identChar_prim.of_eq fun c => by simp))).decide).of_eq
    fun l => by simp [List.all_eq]

theorem pasted_prim : Primrec₂ pasted := by
  have ab : Primrec fun p : String × String => p.1 ++ p.2 := string_append.comp fst snd
  refine (ite_bool (Primrec.and.comp (listAll_ident.comp (string_toList.comp ab))
      (Primrec.not.comp (beq_prim.comp ab (const ""))))
    (option_some.comp ab)
    (ite_bool (Primrec.and.comp (beq_prim.comp fst (const "#")) (beq_prim.comp snd (const "#")))
      (const (some "##")) (const none))).to₂.of_eq fun a b => ?_
  have e1 : (a ++ b).all identChar = (a ++ b).toList.all identChar := String.all_bool_eq
  have e2 : (a ++ b == "") = (a ++ b).isEmpty := by
    rw [Bool.eq_iff_iff]; simp [String.isEmpty_iff]
  unfold pasted
  simp only [e1, e2]

/-- `pasteTwo`, by the cases of its sides. -/
def pasteTwo' (x y : RTok) : Option RTok :=
  if x.isPm then some y else if y.isPm then some x else
  (tokOf x).bind fun a => (tokOf y).bind fun b => (pasted a.s b.s).map fun s => RTok.t { s, H := inter a.H b.H }

theorem pasteTwo_eq (x y : RTok) : pasteTwo x y = pasteTwo' x y := by
  cases x <;> cases y <;> rfl

theorem pasteTwo_prim : Primrec₂ pasteTwo := by
  have h : Primrec fun p : RTok × RTok => pasteTwo' p.1 p.2 :=
    ite_bool (isPm_prim.comp fst) (option_some.comp snd)
      (ite_bool (isPm_prim.comp snd) (option_some.comp fst)
        (option_bind (tokOf_prim.comp fst)
          (option_bind (tokOf_prim.comp (snd.comp fst))
            (option_map (pasted_prim.comp (tok_s.comp (snd.comp fst)) (tok_s.comp snd))
              (rtok_t (tok_mk snd (inter_prim.comp (tok_H.comp (snd.comp (fst.comp fst))) (tok_H.comp (snd.comp fst)))
                (const 0) (const []))).to₂).to₂).to₂))
  exact h.to₂.of_eq fun x y => (pasteTwo_eq x y).symm

theorem pasteStep_prim : Primrec₂ pasteStep := by
  -- p : PState × RTok; inside the `some` case, q : List RTok × Bool
  have pending : Primrec fun r : (PState × RTok) × (List RTok × Bool) =>
      List.casesOn (motive := fun _ => PState) r.2.1 none fun a acc' => (pasteTwo a r.1.2).map fun c => (c :: acc', false) :=
    list_casesOn (fst.comp snd) (const none)
      (option_map (pasteTwo_prim.comp (fst.comp snd) (snd.comp (fst.comp fst)))
        (pair (list_cons.comp snd (snd.comp (snd.comp fst))) (const false)).to₂).to₂
  have idle : Primrec fun r : (PState × RTok) × (List RTok × Bool) =>
      if r.1.2.isOp = true then (if r.2.1.isEmpty = true then none else some (r.2.1, true)) else some (r.1.2 :: r.2.1, false) :=
    ite_bool (isOp_prim.comp (snd.comp fst))
      (ite_bool (list_isEmpty.comp (fst.comp snd))
        (const none) (option_some.comp (pair (fst.comp snd) (const true))))
      (option_some.comp (pair (list_cons.comp (snd.comp fst) (fst.comp snd)) (const false)))
  have h := option_casesOn fst (const none) (ite_bool (snd.comp snd) pending idle).to₂
  exact h.to₂.of_eq fun s x => by
    rcases s with _ | ⟨acc, _ | _⟩
    · rfl
    · rfl
    · cases acc <;> rfl

theorem paste_prim : Primrec paste := by
  have fold : Primrec fun xs : List RTok => xs.foldl pasteStep (some ([], false)) :=
    list_foldl Primrec.id (const _) (pasteStep_prim.comp (fst.comp snd) (snd.comp snd)).to₂
  have fin : Primrec pasteEnd :=
    (option_casesOn Primrec.id (const none)
      (ite_bool (snd.comp snd) (const none) (option_some.comp (list_reverse.comp (fst.comp snd)))).to₂).of_eq
      fun s => by rcases s with _ | ⟨acc, _ | _⟩ <;> rfl
  exact (option_map (fin.comp fold) (listFilterMap snd (tokOf_prim.comp snd).to₂).to₂).of_eq fun xs => by
    unfold paste; rw [← paste_fold]

theorem adjacentPaste_prim : Primrec₂ adjacentPaste := by
  have h : Primrec fun p : List BTok × ℕ =>
      (decide (0 < p.2) && p.1[p.2 - 1]? == some BTok.paste) || p.1[p.2 + 1]? == some BTok.paste :=
    Primrec.or.comp
      (Primrec.and.comp (PrimrecPred.decide (PrimrecRel.comp nat_lt (const 0) snd))
        (beq_prim.comp (list_getElem?.comp fst (nat_sub.comp snd (const 1))) (const (some BTok.paste))))
      (beq_prim.comp (list_getElem?.comp fst (succ.comp snd)) (const (some BTok.paste)))
  exact h.to₂.of_eq fun body i => by unfold adjacentPaste; simp

end PP

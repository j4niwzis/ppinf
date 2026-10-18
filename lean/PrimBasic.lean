/-
  Theorem 9: the machine's small operations are primitive recursive -- fields and
  constructors, characters and strings, hidden-name sets, marks, the environment's lookup.
-/
import PrimEnc

open Primrec

namespace PP

variable {α : Type} [Primcodable α]

/-! Fields and constructors. -/

theorem tok_s : Primrec Tok.s := (fst.comp (of_equiv (e := tokEquiv))).of_eq fun _ => rfl
theorem tok_H : Primrec Tok.H := (fst.comp (snd.comp (of_equiv (e := tokEquiv)))).of_eq fun _ => rfl
theorem tok_o : Primrec Tok.o := (fst.comp (snd.comp (snd.comp (of_equiv (e := tokEquiv))))).of_eq fun _ => rfl
theorem tok_P : Primrec Tok.P := (snd.comp (snd.comp (snd.comp (of_equiv (e := tokEquiv))))).of_eq fun _ => rfl
theorem tok_mk {f : α → String} {g : α → List String} {h : α → ℕ} {k : α → List String}
    (hf : Primrec f) (hg : Primrec g) (hh : Primrec h) (hk : Primrec k) :
    Primrec fun a => Tok.mk (f a) (g a) (h a) (k a) :=
  ((of_equiv_symm (e := tokEquiv)).comp (hf.pair (hg.pair (hh.pair hk)))).of_eq fun _ => rfl

theorem step_mk {f : α → String} {g : α → Tok} {h : α → Option Tok} {k : α → List String} {l : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) (hh : Primrec h) (hk : Primrec k) (hl : Primrec l) :
    Primrec fun a => Step.mk (f a) (g a) (h a) (k a) (l a) :=
  ((of_equiv_symm (e := stepEquiv)).comp (hf.pair (hg.pair (hh.pair (hk.pair hl))))).of_eq fun _ => rfl
theorem step_mark : Primrec Step.mark :=
  (fst.comp (snd.comp (snd.comp (snd.comp (of_equiv (e := stepEquiv)))))).of_eq fun _ => rfl
theorem step_id : Primrec Step.id :=
  (snd.comp (snd.comp (snd.comp (snd.comp (of_equiv (e := stepEquiv)))))).of_eq fun _ => rfl

theorem level_out : Primrec Level.out := (fst.comp (of_equiv (e := levelEquiv))).of_eq fun _ => rfl
theorem level_inp : Primrec Level.inp := (snd.comp (of_equiv (e := levelEquiv))).of_eq fun _ => rfl
theorem level_mk {f g : α → List Tok} (hf : Primrec f) (hg : Primrec g) : Primrec fun a => Level.mk (f a) (g a) :=
  ((of_equiv_symm (e := levelEquiv)).comp (hf.pair hg)).of_eq fun _ => rfl

/-! Characters and strings. -/

theorem char_toNat : Primrec Char.toNat :=
  ((subtype_val (hp := valid_prim)).comp (of_equiv (e := charEquiv))).of_eq fun _ => rfl

theorem string_toList : Primrec String.toList := of_equiv (e := stringEquiv)
theorem string_ofList : Primrec String.ofList := of_equiv_symm (e := stringEquiv)

theorem string_append : Primrec₂ (fun a b : String => a ++ b) :=
  (string_ofList.comp (list_append.comp (string_toList.comp fst) (string_toList.comp snd))).to₂.of_eq
    fun a b => by simp [← String.toList_inj]

/-- `identChar`, on the code point. -/
def identNat (n : ℕ) : Bool :=
  (decide (65 ≤ n) && decide (n ≤ 90)) || (decide (97 ≤ n) && decide (n ≤ 122)) ||
    (decide (48 ≤ n) && decide (n ≤ 57)) || decide (n = 95)

theorem identChar_eq (c : Char) : identChar c = identNat c.toNat := by
  have e : (c == '_') = decide (c.toNat = 95) := by
    rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro h; subst h; rfl
    · intro h; exact Char.toNat_inj.mp (by rw [h]; rfl)
  simp only [identChar, Char.isAlphanum, Char.isAlpha, Char.isUpper, Char.isLower, Char.isDigit, identNat, e,
    UInt32.le_iff_toNat_le, Char.toNat]
  simp only [Bool.or_assoc]
  rfl

theorem identNat_prim : Primrec identNat := by
  unfold identNat
  have le : ∀ k, Primrec fun n : ℕ => decide (k ≤ n) := fun k => (nat_le.comp (const k) Primrec.id).decide
  have ge : ∀ k, Primrec fun n : ℕ => decide (n ≤ k) := fun k => (nat_le.comp Primrec.id (const k)).decide
  exact Primrec.or.comp (Primrec.or.comp (Primrec.or.comp (Primrec.and.comp (le 65) (ge 90))
    (Primrec.and.comp (le 97) (ge 122))) (Primrec.and.comp (le 48) (ge 57)))
    (Primrec.eq.comp Primrec.id (const 95)).decide

theorem identChar_prim : Primrec identChar := (identNat_prim.comp char_toNat).of_eq fun c => (identChar_eq c).symm

/-! Membership and filters, with a parameter. -/

theorem mem_prim {β : Type} [Primcodable β] [DecidableEq β] : PrimrecRel (fun (a : β) (L : List β) => a ∈ L) := by
  have h : PrimrecPred fun p : β × List β => ∃ q ∈ p.2.map (fun b => (p.1, b)), q.1 = q.2 :=
    (PrimrecPred.exists_mem_list (Primrec.eq.comp fst snd)).comp (list_map snd (Primrec.pair (fst.comp fst) snd).to₂)
  have h2 : PrimrecPred fun p : β × List β => p.1 ∈ p.2 := h.of_eq fun p => by simp [eq_comm]
  exact h2.primrecRel

theorem filter_param {β γ : Type} [Primcodable β] [Primcodable γ] {p : β → γ → Bool} (hp : Primrec₂ p)
    {f : α → β} {g : α → List γ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => (g a).filter (p (f a)) := by
  have h1 : Primrec fun a => (g a).map fun b => (f a, b) := list_map hg (Primrec.pair (hf.comp fst) snd).to₂
  have h2 : Primrec fun a => ((g a).map fun b => (f a, b)).filter (fun q => p q.1 q.2) :=
    (listFilter (p := fun q : β × γ => p q.1 q.2 = true) (hp.comp fst snd).primrecPred).comp h1 |>.of_eq
      fun a => by simp
  exact (list_map h2 (snd.comp snd).to₂).of_eq fun a => by
    simp [List.filter_map, Function.comp_def]

/-! Hidden-name sets, marks, the final hidden sets. -/

theorem inter_prim : Primrec₂ inter :=
  (filter_param (p := fun (J : List Name) (h : Name) => decide (h ∈ J)) ((mem_prim.comp snd fst).decide.to₂) snd fst).to₂.of_eq
    fun H J => by simp [inter]

theorem union_prim : Primrec₂ union :=
  (list_append.comp fst (filter_param (p := fun (K : List Name) (h : Name) => decide (h ∉ K))
    ((Primrec.not.comp (mem_prim.comp snd fst).decide).to₂) fst snd)).to₂.of_eq fun K H => by simp [union]

theorem mark_prim : Primrec fun p : ℕ × List Name × List Tok => mark p.1 p.2.1 p.2.2 :=
  (list_map (snd.comp snd) (tok_mk (tok_s.comp snd) (union_prim.comp (fst.comp (snd.comp fst)) (tok_H.comp snd))
    (fst.comp fst) (fst.comp (snd.comp fst))).to₂).of_eq fun p => rfl

theorem finalize_prim : Primrec finalize :=
  (list_map Primrec.id (tok_mk (tok_s.comp snd)
    (Primrec.ite (mem_prim.comp (tok_s.comp snd) (tok_H.comp snd)) (list_cons.comp (tok_s.comp snd) (const [])) (const []))
    (tok_o.comp snd) (tok_P.comp snd)).to₂).of_eq fun xs => rfl

/-! The environment's lookup, `Γ` fixed. -/

theorem find_prim (Γ : Env) : Primrec Γ.find := by
  induction Γ with
  | nil => exact (const none).of_eq fun _ => rfl
  | cons p Γ ih =>
    refine (Primrec.ite (Primrec.eq.comp (const p.1) Primrec.id) (const (some p.2)) ih).of_eq fun m => ?_
    by_cases h : p.1 = m
    · simp [Env.find, List.find?, h]
    · have hb : (p.1 == m) = false := beq_false_of_ne h
      simp [Env.find, List.find?, h, hb]

end PP

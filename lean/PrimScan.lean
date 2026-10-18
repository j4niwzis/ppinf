/-
  Theorem 9: the argument scans are primitive recursive -- `closeAt`, `splitTop`,
  `afterCommas` through their folds, and `bind`.
-/
import PrimBasic
import Folds
import MachineSplit

open Primrec

namespace PP

variable {α σ : Type} [Primcodable α] [Primcodable σ]

theorem ite_bool {c : α → Bool} {f g : α → σ} (hc : Primrec c) (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => if c a = true then f a else g a :=
  (Primrec.cond hc hf hg).of_eq fun a => by cases c a <;> rfl

theorem beq_prim {β : Type} [Primcodable β] [DecidableEq β] [BEq β] [LawfulBEq β] :
    Primrec₂ (fun a b : β => a == b) :=
  (PrimrecRel.decide Primrec.eq).of_eq fun a b => by by_cases h : a = b <;> simp [h]

theorem depth_prim : Primrec₂ depthAfter :=
  (ite_bool (beq_prim.comp (tok_s.comp snd) (const "(")) (succ.comp fst)
    (ite_bool (beq_prim.comp (tok_s.comp snd) (const ")")) (nat_sub.comp fst (const 1)) fst)).to₂.of_eq
    fun d x => by unfold depthAfter; rfl

/-! `closeAt`. -/

theorem closeStep_prim : Primrec₂ closeStep := by
  have d : Primrec fun p : CState × Tok => p.1.1 := fst.comp fst
  have acc : Primrec fun p : CState × Tok => p.1.2.1 := fst.comp (snd.comp fst)
  have remt : Primrec fun p : CState × Tok => p.1.2.2.1.tail := list_tail.comp (fst.comp (snd.comp (snd.comp fst)))
  have xs : Primrec fun p : CState × Tok => p.2.s := tok_s.comp snd
  have none_branch : Primrec fun p : CState × Tok =>
      if (p.2.s == ")") = true then
        (if (p.1.1 == 0) = true then (p.1.1, p.1.2.1, p.1.2.2.1.tail, some (p.1.2.1.reverse, p.2, p.1.2.2.1.tail))
         else (p.1.1 - 1, p.2 :: p.1.2.1, p.1.2.2.1.tail, none))
      else if (p.2.s == "(") = true then (p.1.1 + 1, p.2 :: p.1.2.1, p.1.2.2.1.tail, none)
      else (p.1.1, p.2 :: p.1.2.1, p.1.2.2.1.tail, none) :=
    ite_bool (beq_prim.comp xs (const ")"))
      (ite_bool (beq_prim.comp d (const 0))
        (pair d (pair acc (pair remt (option_some.comp (pair (list_reverse.comp acc) (pair snd remt))))))
        (pair (nat_sub.comp d (const 1)) (pair (list_cons.comp snd acc) (pair remt (const none)))))
      (ite_bool (beq_prim.comp xs (const "("))
        (pair (succ.comp d) (pair (list_cons.comp snd acc) (pair remt (const none))))
        (pair d (pair (list_cons.comp snd acc) (pair remt (const none)))))
  exact (option_casesOn (snd.comp (snd.comp (snd.comp fst))) none_branch (fst.comp fst).to₂).to₂.of_eq
    fun s x => by rcases s with ⟨d, acc, rem, _ | r⟩ <;> rfl

theorem closeAt_prim : Primrec fun xs : List Tok => closeAt 0 xs [] :=
  ((snd.comp (snd.comp snd)).comp (list_foldl Primrec.id (pair (const 0) (pair (const []) (pair Primrec.id (const none))))
    (closeStep_prim.comp (fst.comp snd) (snd.comp snd)).to₂)).of_eq fun xs => closeAt_fold xs 0 []

/-! `splitTop`. -/

theorem splitStep_prim : Primrec₂ splitStep := by
  have d : Primrec fun p : SState × Tok => p.1.1 := fst.comp fst
  have cur : Primrec fun p : SState × Tok => p.1.2.1 := fst.comp (snd.comp fst)
  have G : Primrec fun p : SState × Tok => p.1.2.2 := snd.comp (snd.comp fst)
  exact (ite_bool (Primrec.and.comp (beq_prim.comp (tok_s.comp snd) (const ",")) (beq_prim.comp d (const 0)))
    (pair d (pair (const []) (list_cons.comp (list_reverse.comp cur) G)))
    (pair (depth_prim.comp d snd) (pair (list_cons.comp snd cur) G))).to₂.of_eq fun s x => rfl

theorem splitTop_prim : Primrec fun xs : List Tok => splitTop 0 xs [] := by
  have hf := list_foldl (f := fun xs : List Tok => xs) (g := fun _ => ((0 : ℕ), ([] : List Tok), ([] : List (List Tok))))
    Primrec.id (const _) (splitStep_prim.comp (fst.comp snd) (snd.comp snd)).to₂
  exact ((list_reverse.comp (list_cons.comp (list_reverse.comp (fst.comp snd)) (snd.comp snd))).comp hf).of_eq
    fun xs => by have := splitTop_fold xs 0 [] []; simp only [splitEnd, List.reverse_nil, List.nil_append] at this; exact this

/-! `afterCommas`. -/

theorem commaStep_prim : Primrec₂ commaStep := by
  have k : Primrec fun p : AState × Tok => p.1.1 := fst.comp fst
  have d : Primrec fun p : AState × Tok => p.1.2.1 := fst.comp (snd.comp fst)
  have remt : Primrec fun p : AState × Tok => p.1.2.2.1.tail := list_tail.comp (fst.comp (snd.comp (snd.comp fst)))
  have none_branch : Primrec fun p : AState × Tok =>
      if (p.2.s == "," && p.1.2.1 == 0) = true then
        (if (p.1.1 == 1) = true then (0, p.1.2.1, p.1.2.2.1.tail, some p.1.2.2.1.tail)
         else (p.1.1 - 1, p.1.2.1, p.1.2.2.1.tail, none))
      else (p.1.1, depthAfter p.1.2.1 p.2, p.1.2.2.1.tail, none) :=
    ite_bool (Primrec.and.comp (beq_prim.comp (tok_s.comp snd) (const ",")) (beq_prim.comp d (const 0)))
      (ite_bool (beq_prim.comp k (const 1))
        (pair (const 0) (pair d (pair remt (option_some.comp remt))))
        (pair (nat_sub.comp k (const 1)) (pair d (pair remt (const none)))))
      (pair k (pair (depth_prim.comp d snd) (pair remt (const none))))
  exact (option_casesOn (snd.comp (snd.comp (snd.comp fst))) none_branch (fst.comp fst).to₂).to₂.of_eq
    fun s x => by rcases s with ⟨k, d, rem, _ | r⟩ <;> rfl

theorem afterCommas_prim : Primrec₂ fun (k : ℕ) (xs : List Tok) => afterCommas k 0 xs := by
  have hf := list_foldl (f := fun p : ℕ × List Tok => p.2) (g := fun p => (p.1, (0 : ℕ), p.2, (none : Option (List Tok))))
    snd (pair fst (pair (const 0) (pair snd (const none)))) (commaStep_prim.comp (fst.comp snd) (snd.comp snd)).to₂
  refine (ite_bool (beq_prim.comp fst (const 0)) snd
    (option_getD.comp (snd.comp (snd.comp (snd.comp hf))) (const []))).to₂.of_eq fun k xs => ?_
  cases k with
  | zero => simp [afterCommas]
  | succ k => simpa using afterCommas_fold xs k 0

/-! `bind`. -/

theorem replicate_nil (n : ℕ) : List.replicate n ([] : List Tok) = (List.range n).map fun _ => [] := by
  simp

theorem bind_prim : Primrec fun p : (ℕ × Bool) × List Tok => bind p.1.1 p.1.2 p.2 := by
  have ar : Primrec fun p : (ℕ × Bool) × List Tok => p.1.1 := fst.comp fst
  have va : Primrec fun p : (ℕ × Bool) × List Tok => p.1.2 := snd.comp fst
  have as : Primrec fun p : (ℕ × Bool) × List Tok => splitTop 0 p.2 [] := splitTop_prim.comp snd
  have len : Primrec fun p : (ℕ × Bool) × List Tok => (splitTop 0 p.2 []).length := list_length.comp as
  have rep : Primrec fun p : (ℕ × Bool) × List Tok => List.replicate (p.1.1 - (splitTop 0 p.2 []).length) ([] : List Tok) :=
    (list_map (list_range.comp (nat_sub.comp ar len)) (const []).to₂).of_eq fun p => (replicate_nil _).symm
  have h := ite_bool va
    (Primrec.ite (PrimrecRel.comp nat_lt len ar)
      (ite_bool (Primrec.or.comp (beq_prim.comp (succ.comp len) ar) (beq_prim.comp ar (const 0)))
        (option_some.comp (pair (list_append.comp as rep) (const [])))
        (const none))
      (option_some.comp (pair (list_take.comp ar as) (afterCommas_prim.comp ar snd))))
    (ite_bool (beq_prim.comp ar (const 0))
      (ite_bool (beq_prim.comp as (const [[]])) (option_some.comp (const ([], []))) (const none))
      (ite_bool (beq_prim.comp len ar) (option_some.comp (pair as (const []))) (const none)))
  exact h.of_eq fun p => by unfold bind; rfl

end PP

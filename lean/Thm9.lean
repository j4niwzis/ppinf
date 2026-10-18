import Mathlib.Computability.Primrec.List
import MainBound
import Input
import PrimStep
import Majorant
import Agree

/-!
  Theorem 9 (pp_primrec.tex, §5): every pp-computable function is primitive recursive, against
  Mathlib's `Primrec`.

  The proof, as the paper's: the computation on `F(x̄)` is the machine (Machine, Agree) run a
  number of steps bounded by a primitive recursive function of the input's length (the upper
  bound, MainBound, through the majorant of Majorant); the machine's step is primitive
  recursive (PrimStep), and so is running it that many times, and reading the answer.
-/

open Primrec

namespace PP

/-- `f : ℕᵏ → ℕ` is pp-computable: some environment `Γ` and macro `F` expand
    `F(x̄₁, …, x̄ₖ)` to exactly `f(x̄)` in unary, for every input. -/
def PpComputable {k : Nat} (f : List.Vector Nat k → Nat) : Prop :=
  ∃ (Γ : Env) (F : String), ∀ xs : List.Vector Nat k, ∃ fuel,
    run Γ fuel (call F xs.toList) = some (unaryToks (f xs))

/-- The statement of Theorem 9. -/
def Theorem9 : Prop := ∀ (k : Nat) (f : List.Vector Nat k → Nat), PpComputable f → Primrec f

/-! Reading the answer: the `~` of the output. -/

theorem count_unaryList : ∀ n, (unaryList n).count "~" = n
  | 0 => rfl
  | n + 1 => by
    have ih := count_unaryList n
    unfold unaryList at ih ⊢
    have h1 : List.count "~" ["(", "~", ")"] = 1 := by decide
    rw [List.replicate_succ, List.flatten_cons, List.count_append, ih, h1]; omega

theorem tokenize_unary (n : Nat) : tokenize (unary n) = unaryList n := by
  unfold tokenize unary
  rw [String.toList_ofList, ← List.append_nil (unaryChars n), go_unary, go_nil]
  simp [flushOf]

theorem count_unaryToks (n : Nat) : (unaryToks n).count "~" = n := by
  unfold unaryToks input
  rw [List.map_map]
  simp only [Function.comp_def, List.map_id']
  rw [tokenize_unary, count_unaryList]

/-- What a stopped machine says: the number of `~` it emitted. -/
def answer (st : MState) : Nat :=
  match st.mode with
  | .done out => (out.map (·.s)).count "~"
  | _ => 0

theorem answer_prim : Primrec answer := by
  have cnt : Primrec fun out : List Tok => (out.map (·.s)).count "~" :=
    (list_length.comp (filter_param (p := fun (_ : Unit) (s : String) => s == "~") (beq_prim.comp snd (const "~")).to₂
      (const ()) (list_map Primrec.id (tok_s.comp snd).to₂))).of_eq fun out => by
      rw [List.count_eq_length_filter]; rfl
  have inner : Primrec fun q : MState × ((Frame × List Frame) ⊕ Option (List Tok)) =>
      Sum.casesOn (motive := fun _ => Nat) q.2 (fun _ => 0) (fun o => Option.casesOn (motive := fun _ => Nat) o 0 fun out =>
        (out.map (·.s)).count "~") :=
    sumCasesOn snd (const 0).to₂ (option_casesOn snd (const 0) (cnt.comp snd).to₂).to₂
  refine (sumCasesOn ((of_equiv (e := modeEquiv)).comp mstate_mode) (const 0).to₂ inner.to₂).of_eq fun st => ?_
  rcases st with ⟨m, steps, c⟩
  rcases m with ⟨l, fs⟩ | ⟨f, fs⟩ | out | _ <;> rfl

/-! The input, as a primitive recursive function of the arguments. -/

def argToks' : List Nat → List String
  | [] => []
  | a :: l => unaryList a ++ l.flatMap fun n => "," :: unaryList n

theorem argToks_eq : ∀ l, argToks l = argToks' l
  | [] => rfl
  | [a] => by simp [argToks, argToks']
  | a :: b :: l => by
    have := argToks_eq (b :: l)
    simp only [argToks, argToks', List.map_cons, List.intercalate_cons_cons] at this ⊢
    rw [this]; simp

theorem flatMap_range_const (L : List String) : ∀ n, (List.range n).flatMap (fun _ => L) = (List.replicate n L).flatten
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, flatMap_range_const L n, List.replicate_succ', List.flatten_append]
    simp

theorem unaryList_prim : Primrec unaryList :=
  (list_flatMap (list_range) (const ["(", "~", ")"]).to₂).of_eq fun n => flatMap_range_const _ n

theorem argToks_prim : Primrec argToks :=
  (list_casesOn Primrec.id (const [])
    (list_append.comp (unaryList_prim.comp (fst.comp snd))
      (list_flatMap (snd.comp snd) (list_cons.comp (const ",") (unaryList_prim.comp snd)).to₂)).to₂).of_eq
    fun l => by rw [argToks_eq]; cases l <;> rfl

theorem input_prim (F : String) : Primrec fun xs : List Nat => input (call F xs) :=
  (list_map (list_append.comp (const (tokenize F))
    (list_cons.comp (const "(") (list_append.comp argToks_prim (const [")"]))))
    (tok_mk snd (const []) (const 0) (const [])).to₂).of_eq fun xs => by
    rw [input_call]; simp [List.append_assoc]

/-! The step count. -/

theorem iter_eq (f : Nat → Nat) : ∀ n x, iter f n x = f^[n] x
  | 0, _ => rfl
  | n + 1, x => by rw [Function.iterate_succ_apply', ← iter_eq f n x]; rfl

theorem tcount_eq : ∀ w, tcount w = (fun t => 2 * t + 3)^[w] 1
  | 0 => rfl
  | w + 1 => by rw [Function.iterate_succ_apply', ← tcount_eq w]; rfl

theorem tcount_prim : Primrec tcount :=
  (nat_iterate Primrec.id (const 1)
    ((nat_add.comp (nat_mul.comp (const 2) snd) (const 3)).to₂)).of_eq fun w => (tcount_eq w).symm

theorem Bm_prim (Lb : Nat) : ∀ ρ, Primrec (Bm Lb ρ)
  | 0 => (succ.comp Primrec.id).of_eq fun _ => rfl
  | ρ + 1 => by
    have hF : Primrec (Fm Lb (Bm Lb ρ)) :=
      (nat_mul.comp (const _) (nat_add.comp (nat_add.comp (Bm_prim Lb ρ) Primrec.id) (const 1))).of_eq fun _ => rfl
    exact (nat_iterate tcount_prim Primrec.id (hF.comp snd).to₂).of_eq fun a => by
      show (Fm Lb (Bm Lb ρ))^[tcount a] a = iter (Fm Lb (Bm Lb ρ)) (tcount a) a
      rw [iter_eq]

theorem mcost_eq (b : Nat) : ∀ n, mcost b n = (fun m => (b + 1) * m + 2 * b + 3)^[n] 0
  | 0 => rfl
  | n + 1 => by rw [Function.iterate_succ_apply', ← mcost_eq b n]; rfl

theorem mcost_prim (b : Nat) : Primrec (mcost b) :=
  (nat_iterate Primrec.id (const 0)
    ((nat_add.comp (nat_add.comp (nat_mul.comp (const _) snd) (const _)) (const 3)).to₂)).of_eq
    fun n => (mcost_eq b n).symm

theorem mcost_mono (b : Nat) : ∀ m n, m ≤ n → mcost b m ≤ mcost b n := by
  intro m n h
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (by rw [mcost_succ, Nat.succ_mul]; omega)

/-! **Theorem 9.** -/

/-- The machine's start on `F(x̄)`. -/
def start (F : String) (xs : List Nat) : MState := { mode := .scan ⟨[], input (call F xs)⟩ [], steps := [], c := 1 }

/-- Enough actions for any run on `F(x̄)`. -/
def budget (Γ : Env) (F : String) (xs : List Nat) : Nat :=
  mcost (maxBody Γ) (Bm (maxBody Γ) (names Γ).length (input (call F xs)).length + 2) + 1

theorem answer_eq (Γ : Env) (F : String) (xs : List Nat) (n : Nat)
    (fuel : Nat) (h : run Γ fuel (call F xs) = some (unaryToks n)) :
    answer (mrun Γ (budget Γ F xs) (start F xs)) = n := by
  unfold run at h
  obtain ⟨r, he, hr⟩ := Option.map_eq_some_iff.mp h
  have hin : ∀ t ∈ input (call F xs), t.o = 0 ∧ t.P = [] := by
    intro t ht; simp only [input, List.mem_map] at ht; obtain ⟨_, _, rfl⟩ := ht; exact ⟨rfl, rfl⟩
  have ub := (upper_bound Γ _ hin _ (Nat.le_refl _) fuel 1 r he).1
  have hk : mcost (maxBody Γ) (B (maxBody Γ) (names Γ).length (input (call F xs)).length + 2) + 1 ≤ budget Γ F xs := by
    unfold budget
    have := B_le_Bm (maxBody Γ) (maxBody_pos Γ) (names Γ).length (input (call F xs)).length
    have := mcost_mono (maxBody Γ) _ _ (show B (maxBody Γ) (names Γ).length (input (call F xs)).length + 2 ≤
      Bm (maxBody Γ) (names Γ).length (input (call F xs)).length + 2 by omega)
    omega
  have hm := mexpand_of_expand Γ _ 1 _ r ub _ hk
  unfold mexpand at hm
  unfold answer start
  generalize mrun Γ (budget Γ F xs) { mode := .scan ⟨[], input (call F xs)⟩ [], steps := [], c := 1 } = st at hm ⊢
  rcases st with ⟨m, steps, c⟩
  cases m with
  | done out =>
    simp only [Option.some.injEq] at hm
    subst hm
    simp only at hr ⊢
    have : (finalize out).map (·.s) = out.map (·.s) := by simp [finalize]
    rw [← this, hr, count_unaryToks]
  | scan _ _ => simp at hm
  | body _ _ => simp at hm
  | fail => simp at hm

theorem mstart_prim (F : String) : Primrec fun xs : List Nat => start F xs :=
  (mstate_mk (mode_scan (level_mk (const []) (input_prim F)) (const [])) (const []) (const 1)).of_eq fun _ => rfl

theorem budget_prim (Γ : Env) (F : String) : Primrec fun xs : List Nat => budget Γ F xs :=
  (succ.comp ((mcost_prim _).comp (nat_add.comp ((Bm_prim _ _).comp (list_length.comp (input_prim F))) (const 2)))).of_eq
    fun _ => rfl

theorem theorem9 : Theorem9 := by
  intro k f ⟨Γ, F, hf⟩
  have h : Primrec fun xs : List.Vector Nat k => answer (mrun Γ (budget Γ F xs.toList) (start F xs.toList)) :=
    answer_prim.comp ((mrun_prim Γ).comp ((budget_prim Γ F).comp vector_toList) ((mstart_prim F).comp vector_toList))
  refine h.of_eq fun xs => ?_
  obtain ⟨fuel, hfuel⟩ := hf xs
  exact answer_eq Γ F xs.toList (f xs) fuel hfuel

end PP

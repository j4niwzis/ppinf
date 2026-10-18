/-
  ppinf, pp_primrec.tex: Lemmas 2 (grow) and 5 (cycles need the trick), checked in
  Lean 4 (core only). Hidden sets and marks are predicates on macro names.
-/

variable {α : Type}

def Subset (A B : α → Prop) : Prop := ∀ a, A a → B a

/-- Lemma 2. A non-trick invocation of `m` whose head has origin `e`: head and closing
    parenthesis both carry `P_e` (Lemma 1), `m` is eligible (`m ∉ H`). Then `m ∉ P_e` and
    the new mark `{m} ∪ (H ∩ J)` contains `P_e ∪ {m}`. -/
theorem grow (m : α) (Pe H J : α → Prop)
    (hH : Subset Pe H) (hJ : Subset Pe J) (elig : ¬ H m) :
    ¬ Pe m ∧ Subset (fun a => Pe a ∨ a = m) (fun a => a = m ∨ (H a ∧ J a)) := by
  refine ⟨fun h => elig (hH m h), ?_⟩
  intro a ha
  cases ha with
  | inl h => exact Or.inr ⟨hH a h, hJ a h⟩
  | inr h => exact Or.inl h

/-- A parent chain of non-trick steps: step `i+1` invokes `m (i+1)`, eligible against a hidden
    set containing the mark of step `i`, and its own mark contains the previous one and `m (i+1)`. -/
structure Chain (α : Type) where
  m : Nat → α
  P : Nat → α → Prop
  own : ∀ i, P i (m i)
  keeps : ∀ i, Subset (P i) (P (i + 1))
  eligible : ∀ i, ¬ P i (m (i + 1))

theorem Chain.mono (c : Chain α) {i j : Nat} (h : i ≤ j) : Subset (c.P i) (c.P j) := by
  induction h with
  | refl => exact fun _ x => x
  | step _ ih => exact fun a x => c.keeps _ a (ih a x)

/-- Lemma 5. Along a parent chain without trick steps every macro occurs at most once. -/
theorem Chain.distinct (c : Chain α) {i j : Nat} (h : i < j) : c.m i ≠ c.m j := by
  intro e
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have : c.P k (c.m i) := c.mono (by omega) _ (c.own i)
  exact c.eligible k (e ▸ this)

/-- Hence a chain over finitely many macro names is at most that long: the first `n + 1`
    macros of the chain are pairwise distinct, so they cannot all lie in a list of `n` names. -/
theorem Chain.nodup_prefix (c : Chain α) (n : Nat) : ((List.range n).map c.m).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  refine (List.pairwise_lt_range).imp ?_
  intro i j h
  exact c.distinct h

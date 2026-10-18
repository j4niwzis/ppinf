/-
  Theorem 10: the translation's names decode back to the node (a path of parts) and the
  helper they name, so names of distinct nodes or helpers differ.
-/
import TransEnv

namespace PP

/-- A step down the term: a composition's outer function (`h`) or `j`-th inner one (`k i…i k`),
    a recursion's base (`f`) or step (`r`). -/
inductive Code where
  | h
  | k (j : Nat)
  | f
  | r
  deriving DecidableEq, Repr

def Code.chars : Code → List Char
  | .h => ['h']
  | .k j => 'k' :: List.replicate j 'i' ++ ['k']
  | .f => ['f']
  | .r => ['r']

/-- The macro of the node at a path. -/
def nodeName (path : List Code) : String := String.ofList ('T' :: path.flatMap Code.chars)

/-- The helpers of a recursion node (and the node's own macro, `self`). -/
inductive Helper where
  | self | SEL | SEL2 | TH | STEP | ITER | GEN | GA | GB | GAEND | GBEND | BRA | BRB | BRAEND | BRBEND
  | D1 | D0 | OUT | CAT | CATu | CAT2 | CAT2u
  deriving DecidableEq, Repr

def Helper.suffix : Helper → String
  | .self => "" | .SEL => "SEL" | .SEL2 => "SEL2" | .TH => "TH" | .STEP => "STEP" | .ITER => "ITER"
  | .GEN => "GEN" | .GA => "GA" | .GB => "GB" | .GAEND => "GA_END" | .GBEND => "GB_END" | .BRA => "BRA"
  | .BRB => "BRB" | .BRAEND => "BRA_END" | .BRBEND => "BRB_END" | .D1 => "D1" | .D0 => "D0" | .OUT => "OUT"
  | .CAT => "CAT" | .CATu => "CAT_" | .CAT2 => "CAT2" | .CAT2u => "CAT2_"

def Helper.all : List Helper :=
  [.self, .SEL, .SEL2, .TH, .STEP, .ITER, .GEN, .GA, .GB, .GAEND, .GBEND, .BRA, .BRB, .BRAEND, .BRBEND,
   .D1, .D0, .OUT, .CAT, .CATu, .CAT2, .CAT2u]

theorem Helper.mem_all (x : Helper) : x ∈ Helper.all := by cases x <;> decide

def fullName (path : List Code) (x : Helper) : String := nodeName path ++ x.suffix

/-! Distinct paths and helpers give distinct names. -/

/-- Starts with none of the parts' letters. -/
def NoCode (s : List Char) : Prop := ∀ c r, s = c :: r → c ≠ 'h' ∧ c ≠ 'k' ∧ c ≠ 'f' ∧ c ≠ 'r'

theorem rep_split : ∀ (j j' : Nat) (a b : List Char),
    List.replicate j 'i' ++ 'k' :: a = List.replicate j' 'i' ++ 'k' :: b → j = j' ∧ a = b
  | 0, 0, a, b, h => by simpa using h
  | 0, j' + 1, a, b, h => by simp [List.replicate_succ] at h
  | j + 1, 0, a, b, h => by simp [List.replicate_succ] at h
  | j + 1, j' + 1, a, b, h => by
    simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
    have := rep_split j j' a b h; exact ⟨by omega, this.2⟩

theorem paths_inj : ∀ (p q : List Code) (s t : List Char), NoCode s → NoCode t →
    p.flatMap Code.chars ++ s = q.flatMap Code.chars ++ t → p = q ∧ s = t
  | [], [], s, t, _, _, h => by simpa using h
  | [], c :: q, s, t, hs, _, h => by
    exfalso
    cases c <;> simp [Code.chars] at h <;> (have := hs _ _ h; simp_all)
  | c :: p, [], s, t, _, ht, h => by
    exfalso
    cases c <;> simp [Code.chars] at h <;> (have := ht _ _ h.symm; simp_all)
  | c :: p, d :: q, s, t, hs, ht, h => by
    simp only [List.flatMap_cons, List.append_assoc] at h
    cases c <;> cases d <;> simp [Code.chars] at h
    all_goals first
      | (have := paths_inj p q s t hs ht h; simp_all)
      | (rename_i j j'
         have e := rep_split j j' _ _ (by simpa using h)
         have := paths_inj p q s t hs ht e.2
         simp_all)

theorem suffix_noCode (x : Helper) : NoCode x.suffix.toList := by
  intro c r h
  cases x <;> simp [Helper.suffix] at h <;> (obtain ⟨rfl, _⟩ := h; decide)

theorem suffix_inj (x y : Helper) (h : x.suffix = y.suffix) : x = y := by
  cases x <;> cases y <;> first | rfl | (simp [Helper.suffix] at h)

/-- **Names decode.** -/
theorem fullName_inj {p q : List Code} {x y : Helper} (h : fullName p x = fullName q y) : p = q ∧ x = y := by
  unfold fullName nodeName at h
  have h' := congrArg String.toList h
  simp only [String.toList_append, String.toList_ofList, List.cons_append, List.cons.injEq, true_and] at h'
  obtain ⟨hp, hs⟩ := paths_inj p q _ _ (suffix_noCode x) (suffix_noCode y) h'
  exact ⟨hp, suffix_inj x y (String.toList_inj.mp hs)⟩

end PP

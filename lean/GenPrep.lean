/-
  Theorem 10, recursion, stage D preparation: names of a recursion node's ping-pong, hidden
  sets with punctuation in them, depths of ping-pong outputs, marks of groups.
-/
import Shapes

namespace PP

theorem fullName_ne_helper {π : List Code} {x y : Helper} (h : x ≠ y) : fullName π x ≠ fullName π y :=
  fun e => h (fullName_inj e).2

theorem fullName_ne_end (π : List Code) (x : Helper) : fullName π x ≠ "_END" := fullName_ne (by decide)
theorem fullName_ne_tilde (π : List Code) (x : Helper) : fullName π x ≠ "~" := fullName_ne (by decide)

/-- The ping-pong names of the recursion node `π`. -/
def ppNames {Γ : Env} {f g : Term} {π : List Code} (hR : Realizes Γ (.prec f g) π) : PPNames Γ where
  th := fullName π .TH
  d1 := fullName π .D1
  d0 := fullName π .D0
  out := fullName π .OUT
  thAr := 1
  thBody := [nm π .STEP, prm 0]
  hth := find_prec hR .TH
  hd1 := find_prec hR .D1
  hd0 := find_prec hR .D0
  hout := find_prec hR .OUT
  out_lp := fullName_ne_lp _ _
  d1_lp := fullName_ne_lp _ _
  d1_rp := fullName_ne_rp _ _
  d0_d1 := fullName_ne_helper (by decide)
  out_d1 := fullName_ne_helper (by decide)

/-- Hidden sets of numerals: helpers in `L`, safe names, or anything that is no name. -/
def InJ (π : List Code) (L : List Helper) (H : List Name) : Prop :=
  ∀ n ∈ H, (∃ y ∈ L, n = fullName π y) ∨ Safe π n ∨ ¬ IsName n

theorem not_mem_of_inJ {π : List Code} {L : List Helper} {H : List Name} (h : InJ π L H) {x : Helper} (hx : x ∉ L) :
    fullName π x ∉ H := by
  intro hm
  rcases h _ hm with ⟨y, hy, e⟩ | e | e
  · have := (fullName_inj e).2; subst this; exact hx hy
  · exact e.1 ⟨[], x, by simp⟩
  · exact e ⟨π, x, rfl⟩

theorem inJ_of_in {π : List Code} {L : List Helper} {H : List Name} (h : In π L H) : InJ π L H := by
  intro n hn
  rcases h n hn with e | e
  · exact Or.inl e
  · exact Or.inr (Or.inl e)

/-- A numeral after substitution: finalized, then marked. -/
theorem inJ_marked {π : List Code} {L : List Helper} {K : List Name} (hK : In π L K) {t : Tok}
    (ht : ∀ m ∈ t.H, m = t.s) (hs : ¬ IsName t.s) (c : Nat) : InJ π L (markOne c K t).H := by
  intro n hn
  rcases mem_union.mp hn with h | h
  · exact inJ_of_in hK n h
  · rw [ht n h]; exact Or.inr (Or.inr hs)

theorem punct_not_name {s : String} (hs : s.toList.head? ≠ some 'T') : ¬ IsName s := by
  rintro ⟨π, y, e⟩; exact fullName_ne hs e.symm

/-- The punctuation of a numeral is no name. -/
theorem num_not_name {o : List Tok} {v : Nat} (h : IsNum o v) : ∀ t ∈ o, ¬ IsName t.s := by
  intro t ht
  have : t.s ∈ unaryList v := by rw [← h]; exact List.mem_map_of_mem ht
  rcases mem_unaryList this with e | e | e <;> rw [e] <;> exact punct_not_name (by decide)

/-- The ping-pong head's hidden names. -/
theorem ppInv_of_in {Γ : Env} {f g : Term} {π : List Code} (hR : Realizes Γ (.prec f g) π) {L : List Helper}
    (hL : ∀ y ∈ L, y ≠ .GA ∧ y ≠ .GB ∧ y ≠ .TH ∧ y ≠ .D1 ∧ y ≠ .D0 ∧ y ≠ .OUT) {H : List Name} (h : In π L H)
    (A B : Helper) (hA : A = .GA ∨ A = .GB) (hB : B = .GA ∨ B = .GB) :
    PPInv (ppNames hR) (fullName π A) (fullName π B) H := by
  intro n hn
  right
  rcases h n hn with ⟨y, hy, rfl⟩ | e
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hL y hy
    have hyA : y ≠ A := by rcases hA with rfl | rfl <;> assumption
    have hyB : y ≠ B := by rcases hB with rfl | rfl <;> assumption
    exact ⟨fullName_ne_helper hyA, fullName_ne_helper hyB, fullName_ne_helper h3, fullName_ne_helper h4,
      fullName_ne_helper h5, fullName_ne_helper h6, fullName_ne_lp _ _, fullName_ne_rp _ _⟩
  · have nb : ∀ x, n ≠ fullName π x := fun x en => e.1 ⟨[], x, by simp [en]⟩
    obtain ⟨π', y', rfl⟩ := e.2
    exact ⟨nb _, nb _, nb _, nb _, nb _, nb _, fullName_ne_lp _ _, fullName_ne_rp _ _⟩

/-! Depths of ping-pong outputs. -/

theorem walkS_quads (a b x : String) (ha1 : a ≠ ")") (ha2 : a ≠ "(") (ha3 : a ≠ ",") (hb1 : b ≠ ")") (hb2 : b ≠ "(")
    (hb3 : b ≠ ",") (hx1 : x ≠ ")") (hx2 : x ≠ "(") (hx3 : x ≠ ",") :
    ∀ n, walkS 0 ((List.replicate n [a, b, "(", ")"]).flatten ++ [x]) = some 0
  | 0 => by simp [walkS, hx1, hx2, hx3]
  | n + 1 => by
    rw [List.replicate_succ, List.flatten_cons, List.append_assoc, walkS_append]
    simp [walkS, ha1, ha2, ha3, hb1, hb2, hb3, walkS_quads a b x ha1 ha2 ha3 hb1 hb2 hb3 hx1 hx2 hx3 n]

end PP

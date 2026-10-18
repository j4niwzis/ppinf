/-
  Theorem 10, recursion, stage A: the hidden sets met inside a recursion node -- its own
  helpers so far, and safe names from outside.
-/
import GenCall

namespace PP

/-- Every hidden name is one of the node's helpers in `L`, or safe. -/
def In (π : List Code) (L : List Helper) (H : List Name) : Prop :=
  ∀ n ∈ H, (∃ y ∈ L, n = fullName π y) ∨ Safe π n

theorem in_nil (π : List Code) (L : List Helper) : In π L [] := by intro n h; simp at h

theorem in_mono {π : List Code} {L L' : List Helper} (hL : ∀ y ∈ L, y ∈ L') {H : List Name} (h : In π L H) : In π L' H := by
  intro n hn
  rcases h n hn with ⟨y, hy, e⟩ | e
  · exact Or.inl ⟨y, hL y hy, e⟩
  · exact Or.inr e

theorem in_inter {π : List Code} {L : List Helper} {H : List Name} (h : In π L H) (J : List Name) : In π L (inter H J) :=
  fun n hn => h n (mem_inter.mp hn).1

theorem in_cons {π : List Code} {L : List Helper} {H : List Name} (h : In π L H) (y : Helper) :
    In π (y :: L) (fullName π y :: H) := by
  intro n hn
  rcases List.mem_cons.mp hn with rfl | hn
  · exact Or.inl ⟨y, by simp, rfl⟩
  · exact in_mono (fun z hz => by simp [hz]) h n hn

/-- A mark of a step of helper `y` whose head hides `H`. -/
theorem in_mark {π : List Code} {L : List Helper} {H : List Name} (h : In π L H) (y : Helper) (J : List Name) :
    In π (y :: L) (fullName π y :: inter H J) := in_cons (in_inter h J) y

theorem in_union {π : List Code} {L : List Helper} {K H : List Name} (hK : In π L K) (hH : In π L H) :
    In π L (union K H) := by
  intro n hn
  rcases mem_union.mp hn with h | h
  · exact hK n h
  · exact hH n h

theorem in_markOne {π : List Code} {L : List Helper} {K : List Name} (hK : In π L K) {x : Tok} (hx : In π L x.H) (c : Nat) :
    In π L (markOne c K x).H := in_union hK hx

theorem not_mem_of_in {π : List Code} {L : List Helper} {H : List Name} (h : In π L H) {x : Helper} (hx : x ∉ L) :
    fullName π x ∉ H := by
  intro hm
  rcases h _ hm with ⟨y, hy, e⟩ | e
  · have := (fullName_inj e).2; subst this; exact hx hy
  · exact e.1 ⟨[], x, by simp⟩

theorem name_ne_of_in {π : List Code} {L : List Helper} {H : List Name} (h : In π L H) {s : String}
    (hs : ∀ π' y, fullName π' y ≠ s) : s ∉ H := by
  intro hm
  rcases h _ hm with ⟨y, _, e⟩ | e
  · exact hs π y e.symm
  · obtain ⟨π', y, e'⟩ := e.2; exact hs π' y e'.symm

theorem in_child {π : List Code} {L : List Helper} {H : List Name} (h : In π L H) (c : Code) : ∀ n ∈ H, Safe (π ++ [c]) n := by
  intro n hn
  rcases h n hn with ⟨y, _, rfl⟩ | e
  · exact ⟨not_below_parent π c y, π, y, rfl⟩
  · exact ⟨fun hb => e.1 (below_mono hb), e.2⟩

theorem child_not_in {π : List Code} {L : List Helper} {H : List Name} (h : In π L H) (c : Code) :
    fullName (π ++ [c]) .self ∉ H := by
  intro hm
  rcases h _ hm with ⟨y, _, e⟩ | e
  · have := (fullName_inj e).1; have := congrArg List.length this; simp at this
  · exact e.1 (below_child π c)

/-- The parent's context, seen from inside: its own mark. -/
theorem in_ctx {π : List Code} {x rp : Tok} (hx : x.s = fullName π .self) (hdis : ∀ n ∈ inter x.H rp.H, Safe π n) :
    In π [.self] (x.s :: inter x.H rp.H) := by
  intro n hn
  rcases List.mem_cons.mp hn with rfl | hn
  · exact Or.inl ⟨.self, by simp, hx⟩
  · exact Or.inr (hdis n hn)

/-! Finalized streams whose tokens do not hide their own names hide nothing. -/

theorem finalize_H {xs : List Tok} (h : ∀ t ∈ xs, t.s ∉ t.H) : ∀ t ∈ finalize xs, t.H = [] := by
  intro t ht
  simp only [finalize, List.mem_map] at ht
  obtain ⟨x, hx, rfl⟩ := ht
  simp [h x hx]

theorem in_of_nil {π : List Code} {L : List Helper} {H : List Name} (h : H = []) : In π L H := by subst h; exact in_nil π L

/-! Lookups in a recursion node. -/

theorem find_prec {Γ : Env} {f g : Term} {π : List Code} (h : Realizes Γ (.prec f g) π) (x : Helper) :
    Γ.find (fullName π x) = some (precDef f.arity π x) :=
  h _ (by
    unfold Term.denvP
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨x, by cases x <;> decide, rfl⟩)))

theorem realizes_prec_f {Γ : Env} {f g : Term} {π : List Code} (h : Realizes Γ (.prec f g) π) :
    Realizes Γ f (π ++ [.f]) := fun e he => h e (by simp [Term.denvP, he])

theorem realizes_prec_g {Γ : Env} {f g : Term} {π : List Code} (h : Realizes Γ (.prec f g) π) :
    Realizes Γ g (π ++ [.r]) := fun e he => h e (by simp [Term.denvP, he])

theorem realizes_comp_h {Γ : Env} {k : Nat} {h : Term} {gs : List Term} {π : List Code}
    (hR : Realizes Γ (.comp k h gs) π) : Realizes Γ h (π ++ [.h]) := fun e he => hR e (by simp [Term.denvP, he])

theorem realizes_comp_g {Γ : Env} {k : Nat} {h : Term} {gs : List Term} {π : List Code}
    (hR : Realizes Γ (.comp k h gs) π) (j : Nat) (g : Term) (hg : gs[j]? = some g) : Realizes Γ g (π ++ [.k j]) := by
  intro e he
  apply hR e
  simp only [Term.denvP, List.mem_cons, List.mem_append, List.mem_flatMap]
  right; right
  have hj : j < gs.length := by
    rcases (List.getElem?_eq_some_iff.mp hg) with ⟨hj, _⟩; exact hj
  refine ⟨(⟨g, List.mem_of_getElem? hg⟩, j), ?_, he⟩
  rw [List.mem_zipIdx_iff_getElem?]
  simp [List.getElem?_attach, hg]

end PP

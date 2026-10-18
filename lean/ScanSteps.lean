/-
  Theorem 10: single scanning steps, forward -- a token passed by, a function-like name not
  followed by `(`, a name-free prefix.
-/
import NodeComp2

namespace PP

theorem scan_emit_none (Γ : Env) {x : Tok} (hf : Γ.find x.s = none) {n c : Nat} {rest : List Tok} {q}
    (h : scan Γ n c rest = some q) : scan Γ (n + 1) c (x :: rest) = some (x :: q.1, q.2.1, q.2.2) := by
  unfold scan
  by_cases hid : x.s ∈ x.H
  · simp [hid, emit, h]
  · simp [hid, hf, emit, h]

theorem scan_emit_fn (Γ : Env) {x y : Tok} {ar : Nat} {va : Bool} {body : List BTok}
    (hf : Γ.find x.s = some (.fn ar va body)) (hy : y.s ≠ "(") {n c : Nat} {rest : List Tok} {q}
    (h : scan Γ n c (y :: rest) = some q) : scan Γ (n + 1) c (x :: y :: rest) = some (x :: q.1, q.2.1, q.2.2) := by
  unfold scan
  have hy' : (y.s != "(") = true := by simpa using hy
  by_cases hid : x.s ∈ x.H
  · simp [hid, emit, h]
  · simp [hid, hf, hy', emit, h]

theorem scan_fn_last (Γ : Env) {x : Tok} {ar : Nat} {va : Bool} {body : List BTok}
    (hf : Γ.find x.s = some (.fn ar va body)) (n c : Nat) : scan Γ (n + 2) c [x] = some ([x], [], c) := by
  unfold scan
  by_cases hid : x.s ∈ x.H
  · simp [hid, emit, scan]
  · simp [hid, hf]

theorem scan_nameFree_prefix (Γ : Env) : ∀ (l : List Tok), NameFree Γ l → ∀ {n c : Nat} {rest : List Tok} {q},
    scan Γ n c rest = some q → scan Γ (n + l.length) c (l ++ rest) = some (l ++ q.1, q.2.1, q.2.2)
  | [], _, n, c, rest, q, h => by simpa using h
  | x :: l, hl, n, c, rest, q, h => by
    have := scan_nameFree_prefix Γ l (fun t ht => hl t (by simp [ht])) h
    have h2 := scan_emit_none Γ (hl x (by simp)) this
    simp only [List.length_cons, List.cons_append]
    rw [show n + (l.length + 1) = n + l.length + 1 by omega]
    simpa using h2

end PP

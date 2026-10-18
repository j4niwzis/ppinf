/-
  pp_primrec.tex, Theorem 6 (upper bound): the hierarchy Φ, checked in Lean 4 (core only).

      Φ₀(x) = 2x,    Φ_N(x) = Φ_{N-1}^{(x)}(x)   (N ≥ 1)

  What is checked: Φ₁(x) = x·2^x; each Φ_N is monotone and inflationary; the step of the
  proof's induction, (Φ_N^{(p)})^{(x)}(y) ≤ Φ_{N+1}(p·y) for p ≥ 1, x ≤ y; and that the bound
  needs its iterate: EXPONENTIAL(EXPONENTIAL(s)), level 1, gives 2^(2^n), which no Φ₁(cn+d)
  bounds.
-/

/-- `f` applied `n` times. -/
def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => f (iter f n x)

def Φ : Nat → Nat → Nat
  | 0, x => 2 * x
  | N + 1, x => iter (Φ N) x x

theorem iter_double (n x : Nat) : iter (fun y => 2 * y) n x = 2 ^ n * x := by
  induction n with
  | zero => simp [iter]
  | succ n ih => simp only [iter, ih, Nat.pow_succ]; rw [Nat.mul_comm (2 ^ n) 2, Nat.mul_assoc]

theorem Φ_one (x : Nat) : Φ 1 x = 2 ^ x * x := by
  simp only [Φ, iter_double]

theorem Φ_one_dominates_two_pow (n : Nat) : 2 ^ n ≤ Φ 1 (n + 1) := by
  rw [Φ_one, Nat.pow_succ]
  have : 2 ^ n ≤ 2 ^ n * 2 := Nat.le_mul_of_pos_right _ (by decide)
  exact Nat.le_trans this (Nat.le_mul_of_pos_right _ (by omega))

/-! Monotone and inflationary, at every level. -/

theorem iter_mono {f : Nat → Nat} (hf : ∀ a b, a ≤ b → f a ≤ f b) (n : Nat) :
    ∀ a b, a ≤ b → iter f n a ≤ iter f n b := by
  induction n with
  | zero => intro a b h; exact h
  | succ n ih => intro a b h; exact hf _ _ (ih a b h)

theorem iter_infl {f : Nat → Nat} (hf : ∀ a, a ≤ f a) (n a : Nat) : a ≤ iter f n a := by
  induction n with
  | zero => exact Nat.le_refl a
  | succ n ih => exact Nat.le_trans ih (hf _)

theorem iter_more {f : Nat → Nat} (hf : ∀ a, a ≤ f a) (a : Nat) :
    ∀ m n, m ≤ n → iter f m a ≤ iter f n a := by
  intro m n h
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (hf _)

theorem Φ_props : ∀ N, (∀ a b, a ≤ b → Φ N a ≤ Φ N b) ∧ (∀ a, a ≤ Φ N a) := by
  intro N
  induction N with
  | zero => exact ⟨fun a b h => by simp only [Φ]; omega, fun a => by simp only [Φ]; omega⟩
  | succ N ih =>
    obtain ⟨mono, infl⟩ := ih
    refine ⟨fun a b h => ?_, fun a => ?_⟩
    · simp only [Φ]
      exact Nat.le_trans (iter_mono mono a a b h) (iter_more infl b a b h)
    · simp only [Φ]; exact iter_infl infl a a

theorem Φ_mono (N : Nat) {a b : Nat} (h : a ≤ b) : Φ N a ≤ Φ N b := (Φ_props N).1 a b h
theorem Φ_infl (N a : Nat) : a ≤ Φ N a := (Φ_props N).2 a

/-! The step of the proof's induction. -/

theorem iter_add (f : Nat → Nat) (k : Nat) : ∀ p z, iter f p (iter f k z) = iter f (k + p) z := by
  intro p z
  induction p with
  | zero => rfl
  | succ p ih => simp only [iter, ih]; rfl

theorem iter_iter (f : Nat → Nat) (p : Nat) : ∀ x y, iter (iter f p) x y = iter f (p * x) y := by
  intro x
  induction x with
  | zero => intro y; simp [iter]
  | succ x ih =>
    intro y
    rw [Nat.mul_succ]
    simp only [iter, ih]
    exact iter_add f _ p y

/-- A pass of at most `x` steps, each bounded by a `p`-fold iterate of level `N`, from
    `y ≥ x`, stays under level `N + 1` at `p y`. -/
theorem pass_bound (N p x y : Nat) (hp : 1 ≤ p) (hxy : x ≤ y) :
    iter (iter (Φ N) p) x y ≤ Φ (N + 1) (p * y) := by
  rw [iter_iter]
  simp only [Φ]
  have h1 : iter (Φ N) (p * x) y ≤ iter (Φ N) (p * x) (p * y) :=
    iter_mono (fun a b h => Φ_mono N h) _ _ _ (Nat.le_mul_of_pos_left y hp)
  exact Nat.le_trans h1 (iter_more (Φ_infl N) _ _ _ (Nat.mul_le_mul_left p hxy))

/-! The iterate is needed: 2^(2^n) (EXPONENTIAL composed with itself, level 1) is above
    every Φ₁(cn+d). -/

theorem no_linear_bound_on_two_pow (c d : Nat) : ∃ n, c * n + d < 2 ^ n := by
  -- n = 3k with k = c + d + 1:  c·3k + d < 3k² + k ≤ (k+1)³ ≤ (2^k)³ = 2^(3k)
  let k := c + d + 1
  refine ⟨3 * k, ?_⟩
  have hk : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  have h3 : (k + 1) * (k + 1) * (k + 1) ≤ 2 ^ k * 2 ^ k * 2 ^ k :=
    Nat.mul_le_mul (Nat.mul_le_mul hk hk) hk
  have hpow : 2 ^ (3 * k) = 2 ^ k * 2 ^ k * 2 ^ k := by
    rw [show 3 * k = k + k + k by omega, Nat.pow_add, Nat.pow_add]
  rw [hpow]
  have hc : c < k := by omega
  have h1 : c * (3 * k) < k * (3 * k) := Nat.mul_lt_mul_of_pos_right hc (by omega)
  have h2 : k * (3 * k) + k ≤ (k + 1) * (k + 1) * (k + 1) := by
    have e : (k + 1) * (k + 1) * (k + 1) = k * k * k + 3 * (k * k) + 3 * k + 1 := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]; omega
    have e2 : k * (3 * k) = 3 * (k * k) := by
      rw [Nat.mul_left_comm]
    omega
  omega

theorem Φ_one_le (y : Nat) : Φ 1 y ≤ 2 ^ (2 * y) := by
  rw [Φ_one, show 2 * y = y + y by omega, Nat.pow_add]
  exact Nat.mul_le_mul_left _ (Nat.le_of_lt Nat.lt_two_pow_self)

theorem composed_exponentials_beat_level_one (c d : Nat) : ∃ n, Φ 1 (c * n + d) < 2 ^ 2 ^ n := by
  obtain ⟨n, hn⟩ := no_linear_bound_on_two_pow (2 * c) (2 * d)
  refine ⟨n, Nat.lt_of_le_of_lt (Φ_one_le _) ?_⟩
  exact Nat.pow_lt_pow_right (by decide) (by rw [Nat.mul_add, ← Nat.mul_assoc]; exact hn)

/-! The values the paper reports. -/
def tower : Nat → Nat
  | 0 => 1
  | n + 1 => 2 ^ tower n

example : (List.range 4).map (fun n => tower (n + 1)) = [2, 4, 16, 65536] := by decide
example : [1, 2, 3, 5].map (2 ^ ·) = [2, 4, 8, 32] := by decide
example : (List.range 4).map (fun n => 2 ^ 2 ^ (n + 1)) = [4, 16, 256, 65536] := by decide

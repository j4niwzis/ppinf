/-
  Primitive recursive functions, as Mathlib's `Nat.Primrec` defines them: built from zero,
  successor, the two halves of a pairing, pairing, composition and primitive recursion --
  here with the pairing 2^a (2b+1) - 1, whose halves are read off by halving.
-/

namespace PR

/-- How many times 2 divides `m` (0 for 0). -/
def v2 (m : Nat) : Nat := if h : m ≠ 0 ∧ m % 2 = 0 then v2 (m / 2) + 1 else 0
termination_by m
decreasing_by omega

def pair (a b : Nat) : Nat := 2 ^ a * (2 * b + 1) - 1

def unpair (n : Nat) : Nat × Nat :=
  let v := v2 (n + 1)
  (v, ((n + 1) / 2 ^ v - 1) / 2)

theorem v2_odd (b : Nat) : v2 (2 * b + 1) = 0 := by
  unfold v2; simp; omega

theorem v2_mul2 (m : Nat) (h : m ≠ 0) : v2 (2 * m) = v2 m + 1 := by
  rw [v2]; simp only [ne_eq, Nat.mul_eq_zero, h, or_false, Nat.mul_mod_right, and_true]
  rw [dif_pos (by omega)]
  rw [Nat.mul_div_cancel_left _ (by decide)]

theorem pow_pos' (a : Nat) : 0 < 2 ^ a := Nat.pos_pow_of_pos a (by decide)

theorem v2_pair (a b : Nat) : v2 (2 ^ a * (2 * b + 1)) = a := by
  induction a with
  | zero => simp [v2_odd]
  | succ a ih =>
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc, v2_mul2 _ (by
      have := pow_pos' a; exact Nat.ne_of_gt (Nat.mul_pos this (by omega))), ih]

theorem pair_succ (a b : Nat) : pair a b + 1 = 2 ^ a * (2 * b + 1) := by
  unfold pair
  have : 0 < 2 ^ a * (2 * b + 1) := Nat.mul_pos (pow_pos' a) (by omega)
  omega

@[simp] theorem unpair_pair (a b : Nat) : unpair (pair a b) = (a, b) := by
  unfold unpair
  simp only
  rw [pair_succ, v2_pair, Nat.mul_div_cancel_left _ (pow_pos' a)]
  simp

theorem le_pair_right (a b : Nat) : b ≤ pair a b := by
  have h := pair_succ a b
  have : 2 * b + 1 ≤ 2 ^ a * (2 * b + 1) := Nat.le_mul_of_pos_left _ (pow_pos' a)
  omega

theorem le_pair_left (a b : Nat) : a ≤ pair a b := by
  have h := pair_succ a b
  have : a < 2 ^ a := Nat.lt_two_pow_self
  have : 2 ^ a ≤ 2 ^ a * (2 * b + 1) := Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- The second half never exceeds the number. -/
theorem unpair_right_le (n : Nat) : (unpair n).2 ≤ n := by
  unfold unpair
  simp only
  have : (n + 1) / 2 ^ v2 (n + 1) ≤ n + 1 := Nat.div_le_self _ _
  omega

theorem v2_le (m : Nat) : v2 m ≤ m := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    rw [v2]
    split
    · rename_i h
      have := ih (m / 2) (by omega)
      omega
    · omega

theorem unpair_left_le (n : Nat) : (unpair n).1 ≤ n + 1 := by
  unfold unpair; simp only; exact v2_le _

/-- Primitive recursive functions of one number (pairs encode tuples). -/
inductive Prim : (Nat → Nat) → Prop where
  | zero : Prim fun _ => 0
  | succ : Prim Nat.succ
  | left : Prim fun n => (unpair n).1
  | right : Prim fun n => (unpair n).2
  | pair {f g : Nat → Nat} : Prim f → Prim g → Prim fun n => pair (f n) (g n)
  | comp {f g : Nat → Nat} : Prim f → Prim g → Prim fun n => f (g n)
  | prec {f g : Nat → Nat} : Prim f → Prim g →
      Prim fun n => (Nat.rec (motive := fun _ => Nat) (f (unpair n).1)
        (fun y IH => g (PR.pair (unpair n).1 (PR.pair y IH))) (unpair n).2)

end PR

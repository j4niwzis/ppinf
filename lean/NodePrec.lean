/-
  Theorem 10, the node lemma for primitive recursion.
-/
import SelStage

namespace PP

def precBody (π : List Code) (m : Nat) : List BTok :=
  [nm π .SEL, tk "(", nm π .ITER, tk "(", prm 0, tk ",", tk "(", tk ",", nm (π ++ [.f]) .self, tk "("] ++
    joinB ((prms m 1).map ([·])) ++ [tk ")"] ++ tailB (prms m 1) ++ [tk ")", tk ")", tk ")"]

theorem precDef_self (m : Nat) (π : List Code) : precDef m π .self = .fn (m + 1) false (precBody π m) := rfl

/-- The base: `( , f ( ȳ ) , ȳ )`. -/
def baseToks (π : List Code) (Y1 Y2 : List (List Tok)) : List Tok :=
  { s := "(" } :: comma :: (callToks { s := fullName (π ++ [.f]) .self } { s := "(" } comma { s := ")" } Y1 ++
    ((Y2.flatMap fun o => comma :: o) ++ [{ s := ")" }]))

theorem prms_single_off (m s : Nat) : (prms m s).map ([·]) = ((List.range m).map (s + ·)).map fun i => [prm i] := by
  simp [prms, Function.comp_def]

theorem paramIdx_prec (π : List Code) (m : Nat) :
    paramIdx (precBody π m) = [0] ++ (List.range m).map (1 + ·) ++ (List.range m).map (1 + ·) := by
  unfold precBody
  simp only [paramIdx_append]
  rw [prms_single_off, paramIdx_joinB_single, prms_eq, paramIdx_tailB]
  simp [nm, tk, prm, paramIdx]

theorem toks_prec (π : List Code) (m : Nat) (oN : List Tok) (Y1 Y2 : List (List Tok)) (h1 : Y1.length = m)
    (h2 : Y2.length = m) :
    toks (plainOut (precBody π m) ([oN] ++ Y1 ++ Y2)) =
      callToks { s := fullName π .SEL } { s := "(" } comma { s := ")" }
        [callToks { s := fullName π .ITER } { s := "(" } comma { s := ")" } [oN, baseToks π Y1 Y2]] := by
  unfold precBody
  let B1 : List BTok := [nm π .SEL, tk "(", nm π .ITER, tk "(", prm 0, tk ",", tk "(", tk ",", nm (π ++ [.f]) .self, tk "("]
  let J : List BTok := joinB ((prms m 1).map ([·]))
  let T : List BTok := tailB (prms m 1)
  have pB1 : paramIdx B1 = [0] := by simp [B1, nm, tk, prm, paramIdx]
  have pJ : paramIdx J = (List.range m).map (1 + ·) := by simp only [J, prms_single_off, paramIdx_joinB_single]
  have pT : paramIdx T = (List.range m).map (1 + ·) := by simp only [T, prms_eq, paramIdx_tailB]
  rw [show [oN] ++ Y1 ++ Y2 = ((([oN] ++ Y1) ++ []) ++ Y2) ++ [] by simp]
  rw [plainOut_append (((B1 ++ J) ++ [tk ")"]) ++ T) [tk ")", tk ")", tk ")"] ((([oN] ++ Y1) ++ []) ++ Y2) [] (by
      simp only [paramIdx_append, pB1, pJ, pT]; simp [tk, paramIdx, h1, h2])]
  rw [plainOut_append ((B1 ++ J) ++ [tk ")"]) T (([oN] ++ Y1) ++ []) Y2 (by
      simp only [paramIdx_append, pB1, pJ]; simp [tk, paramIdx, h1])]
  rw [plainOut_append (B1 ++ J) [tk ")"] ([oN] ++ Y1) [] (by simp only [paramIdx_append, pB1, pJ]; simp [h1])]
  rw [plainOut_append B1 J [oN] Y1 (by rw [pB1]; rfl)]
  have hJ : toks (plainOut J Y1) = joinArgs comma Y1 := by
    simp only [J, prms_single_off]; exact toks_joinB_single _ Y1 (by simp [h1])
  have hT : toks (plainOut T Y2) = Y2.flatMap fun o => comma :: o := by
    simp only [T, prms_eq]; exact toks_tailB _ Y2 (by simp [h2])
  simp only [toks_append]; rw [hJ, hT]
  simp only [B1, nm, tk, prm, plainOut, toks_t, toks_map_t]
  simp [toks, tokOf, callToks, joinArgs, baseToks, comma]

end PP

/-
  The semantics on ppinf.h itself, against what clang -E gives (pp_primrec.tex §4–5):
  EXPONENTIAL 2^n, TOWER 2↑↑n, ADD a+b, EXP2 2^(2^n), and the sequence operations.
-/
import Read

namespace PP

def ppinf : Env := defines (include_str "../ppinf.h")

def extra : Env := defines "
#define PCAT(a,b) PCAT_(a,b)
#define PCAT_(a,b) a##b
#define SUCC(s) s (~)
#define GEN_SUCC_A(...) SUCC DELAY_OPEN_BRACE_1() GEN_SUCC_B
#define GEN_SUCC_B(...) SUCC DELAY_OPEN_BRACE_1() GEN_SUCC_A
#define GEN_SUCC_A_END
#define GEN_SUCC_B_END
#define ADD(a,b) PCAT(PCAT(GEN_SUCC_A b, _END)(a) GEN_BRACE_2_A b, _END)
#define TCAT(a, b) TCAT_(a, b)
#define TCAT_(a, b) a##b
#define TGEN_EXP_A(...) EXPONENTIAL DELAY_OPEN_BRACE_1() TGEN_EXP_B
#define TGEN_EXP_B(...) EXPONENTIAL DELAY_OPEN_BRACE_1() TGEN_EXP_A
#define TGEN_EXP_A_END
#define TGEN_EXP_B_END
#define TCLOSE_A(...) ) TCLOSE_B
#define TCLOSE_B(...) ) TCLOSE_A
#define TCLOSE_A_END
#define TCLOSE_B_END
#define TOWER(seq) TCAT(TCAT(TGEN_EXP_A seq, _END)(~) TCLOSE_A seq, _END)
#define EXP2(s) EXPONENTIAL(EXPONENTIAL(s))
"

def Γ : Env := extra ++ ppinf

def fuel : Nat := 10000000

def seqOf (n : Nat) : String := String.join ((List.range n).map fun i => s!"(a{i})")
def nat (n : Nat) : String := String.join (List.replicate n "(~)")

def countOf (e : String) : Option Nat := (run Γ fuel e).map groups

example : [1, 2, 3, 5].map (fun n => countOf s!"EXPONENTIAL({seqOf n})") = [2, 4, 8, 32].map some := by native_decide
example : [1, 2, 3, 4].map (fun n => countOf s!"TOWER({seqOf n})") = [2, 4, 16, 65536].map some := by native_decide
example : [(3, 2), (1, 4), (0, 3), (2, 0)].map (fun (a, b) => countOf s!"ADD({nat a}, {nat b})") = [5, 5, 3, 2].map some := by native_decide
example : [1, 2, 3, 4].map (fun n => countOf s!"EXP2({seqOf n})") = [4, 16, 256, 65536].map some := by native_decide

-- The sequence operations, as ppinf.h's comments and §4 have them.
example : run Γ fuel "ZIP((a)(b)(c), (d)(e)(f))" = some (tokenize "(a, d)(b, e)(c, f)") := by native_decide
example : run Γ fuel "EQUAL_LENGTH((a)(b)(c), (c)(d))" = some ["NO"] := by native_decide
example : run Γ fuel "EQUAL_LENGTH((a)(), (c)(d))" = some ["YES"] := by native_decide
example : run Γ fuel "SLIDE_2((a)(b)(c))" = some (tokenize "(a, b)(b, c)") := by native_decide
example : run Γ fuel "SLIDE_3((a)(b)(c)(d)(e)(f))" = some (tokenize "(a, b, c)(b, c, d)(c, d, e)(d, e, f)") := by native_decide

end PP

import TransEnvP
open PP
def sameEnvP (t : Term) : Bool :=
  let d := t.denvP []
  d.length == t.env.length && d.all fun (n, df) => toString (repr (t.env.find n)) == toString (repr (some df))
#eval [addT, mulT, predT, subT, exp2T, Term.comp 2 mulT [Term.proj 2 1, Term.comp 2 Term.succ [Term.zero 2]]].map sameEnvP
#eval (fullName [] .self, fullName [.k 2, .r] .GAEND)

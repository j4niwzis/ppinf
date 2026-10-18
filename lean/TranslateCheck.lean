import Translate
open PP
#eval [(3,2),(1,4),(0,3),(2,0)].map fun (a, b) => (runTerm addT 1000000 [a, b], addT.eval [a, b])
#eval [(3,2),(2,4),(0,3),(2,0)].map fun (a, b) => (runTerm mulT 1000000 [a, b], mulT.eval [a, b])
#eval [0,1,2,5].map fun a => (runTerm predT 1000000 [a], predT.eval [a])
#eval [(3,5),(5,3),(0,3),(2,2)].map fun (a, b) => (runTerm subT 1000000 [a, b], subT.eval [a, b])
#eval [0,1,2,3,4].map fun a => (runTerm exp2T 10000000 [a], exp2T.eval [a])

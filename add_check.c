#include "ppinf-main/ppinf.h"
#define PCAT(a,b) PCAT_(a,b)
#define PCAT_(a,b) a##b
#define SUCC(s) s (~)
/* ITER(F)(count)(seed): применить F ровно |count| раз к seed.
   как EXPONENTIAL: пасс порождает "F DELAY_OPEN_BRACE_1()" на каждую группу, второй пасс — ")". */
#define GEN_SUCC_A(...) SUCC DELAY_OPEN_BRACE_1() GEN_SUCC_B
#define GEN_SUCC_B(...) SUCC DELAY_OPEN_BRACE_1() GEN_SUCC_A
#define GEN_SUCC_A_END
#define GEN_SUCC_B_END
#define ADD(a,b) PCAT(PCAT(GEN_SUCC_A b, _END)(a) GEN_BRACE_2_A b, _END)
ADD((~)(~)(~), (~)(~))
ADD((~), (~)(~)(~)(~))
ADD(, (~)(~)(~))
ADD((~)(~), )

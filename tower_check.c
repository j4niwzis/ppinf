#include "ppinf-main/ppinf.h"
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
TOWER((a))
TOWER((a)(b))
TOWER((a)(b)(c))
TOWER((a)(b)(c)(d))

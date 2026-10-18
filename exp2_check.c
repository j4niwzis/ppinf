#include "ppinf-main/ppinf.h"
/* EXPONENTIAL composed with itself: level 1, 2^(2^n) groups. */
#define EXP2(s) EXPONENTIAL(EXPONENTIAL(s))
EXP2((a))
EXP2((a)(b))
EXP2((a)(b)(c))
EXP2((a)(b)(c)(d))

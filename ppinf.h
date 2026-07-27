#define EVAL2(...) __VA_ARGS__

#define OUT

#define VOID(...)

#define DELAY_OUT_0() OUT
#define DELAY_OUT_1() DELAY_OUT_0 OUT()
#define DELAY_OUT_2() DELAY_OUT_1 OUT()
#define DELAY_OUT_3() DELAY_OUT_2 OUT()
#define DELAY_OUT_4() DELAY_OUT_3 OUT()
#define DELAY_OUT_5() DELAY_OUT_4 OUT()

#define DELAY_COMMA_0() ,
#define DELAY_COMMA_1() DELAY_COMMA_0 OUT()
#define DELAY_COMMA_2() DELAY_COMMA_1 OUT()
#define DELAY_COMMA_3() DELAY_COMMA_2 OUT()

#define DELAY_OPEN_BRACE_0() (
#define DELAY_OPEN_BRACE_1() DELAY_OPEN_BRACE_0 OUT()
#define DELAY_OPEN_BRACE_2() DELAY_OPEN_BRACE_1 OUT()
#define DELAY_OPEN_BRACE_3() DELAY_OPEN_BRACE_2 OUT()

#define DELAY_CLOSE_BRACE_0() )
#define DELAY_CLOSE_BRACE_1() DELAY_CLOSE_BRACE_0 OUT()
#define DELAY_CLOSE_BRACE_2() DELAY_CLOSE_BRACE_1 OUT()
#define DELAY_CLOSE_BRACE_3() DELAY_CLOSE_BRACE_2 OUT()

#define CAT(a, b) CAT_(a, b)
#define CAT_(a, b) a##b

#define TEST_NULL_NULL 0,

#define IF_ELSE_1(test, next, ...) next OUT
#define IF_ELSE_0(test, next, ...) IF_ELSE_1(test, next, __VA_ARGS__, 0)

#define IF_ELSE(condition, t, f) IF_ELSE_0(condition OUT t, f, 0)

#define IF_ELSE_NO_OUT_1(test, next, ...) next
#define IF_ELSE_NO_OUT_0(test, next, ...) IF_ELSE_NO_OUT_1(test, next, __VA_ARGS__, 0)

#define IF_ELSE_NO_OUT(condition, t, f) IF_ELSE_NO_OUT_0(condition OUT t, f, 0)

#define SLIDE_2_A(x) \
  IF_ELSE_NO_OUT(    \
      CAT(TEST_NULL_, x), RIGHT_EDGE DELAY_CLOSE_BRACE_2(), x DELAY_CLOSE_BRACE_2() DELAY_OPEN_BRACE_2() x DELAY_COMMA_2() SLIDE_2_B)
#define SLIDE_2_B(x) \
  IF_ELSE_NO_OUT(    \
      CAT(TEST_NULL_, x), RIGHT_EDGE DELAY_CLOSE_BRACE_2(), x DELAY_CLOSE_BRACE_2() DELAY_OPEN_BRACE_2() x DELAY_COMMA_2() SLIDE_2_A)

#define SLIDE_2_(seq) ( LEFT_EDGE, SLIDE_2_A seq(NULL)

#define WRAP_SEQ_A(...) (VALUE(__VA_ARGS__)) WRAP_SEQ_B
#define WRAP_SEQ_B(...) (VALUE(__VA_ARGS__)) WRAP_SEQ_A
#define WRAP_SEQ_A_END
#define WRAP_SEQ_B_END
#define WRAP_SEQ(seq) CAT(WRAP_SEQ_A seq, _END)

#define TEST_RIGHT_EDGE_RIGHT_EDGE 0,

#define REMOVE_EDGES_A(a, b) IF_ELSE(CAT(TEST_RIGHT_EDGE_, b), , (a, b)) REMOVE_EDGES_B
#define REMOVE_EDGES_B(a, b) IF_ELSE(CAT(TEST_RIGHT_EDGE_, b), , (a, b)) REMOVE_EDGES_A
#define REMOVE_EDGES_A_END
#define REMOVE_EDGES_B_END
#define REMOVE_EDGES(seq) EVAL2(VOID CAT(REMOVE_EDGES_A seq, _END))

#define SLIDE_2(seq) REMOVE_EDGES(SLIDE_2_(seq))

#define FIRST_VALUE(a, b) a
#define SECOND_VALUE(a, b) b

#define SLIDE_3_A(a, b) (FIRST_##a, SECOND_##a, SECOND_##b) SLIDE_3_B
#define SLIDE_3_B(a, b) (FIRST_##a, SECOND_##a, SECOND_##b) SLIDE_3_A
#define SLIDE_3_A_END
#define SLIDE_3_B_END

#define SLIDE_3_HELPER(seq) CAT(SLIDE_3_A seq, _END)
#define SLIDE_3(seq) SLIDE_3_HELPER(SLIDE_2(WRAP_SEQ(SLIDE_2(seq))))

#define TEST_BRACE(...) 0,

#define UNWRAP(x, y, z) IF_ELSE(TEST_BRACE y, y, )(x, z)
#define UNWRAP_2(...) UNWRAP __VA_ARGS__

#define TEST_A(x) UNWRAP_2 DELAY_OPEN_BRACE_1() TEST_B
#define TEST_B(x) UNWRAP_2 DELAY_OPEN_BRACE_1() TEST_A
#define TEST_A_END
#define TEST_B_END

#define NESTED_1_A(...) (__VA_ARGS__, NESTED_1_B
#define NESTED_1_B(...) (__VA_ARGS__, NESTED_1_A

#define NESTED_2_TEST(x, y) 0,

#define NESTED_2_A(...) , __VA_ARGS__) NESTED_2_B
#define NESTED_2_B(...) , __VA_ARGS__) NESTED_2_A
#define NESTED_2_A_END
#define NESTED_2_B_END
#define NESTED_3_A(x) ) NESTED_3_B
#define NESTED_3_B(x) ) NESTED_3_A
#define NESTED_3_A_END
#define NESTED_3_B_END

#define ZIP_(seq, seq2) CAT(CAT(EVAL2(CAT(TEST_A seq, _END) NESTED_1_A seq NESTED_2_A seq2 NESTED_3_A seq), _END), _END)

#define REVERSE_A(x, y) (x) REVERSE_B
#define REVERSE_B(x, y) (x) REVERSE_A
#define REVERSE_A_END
#define REVERSE_B_END
#define REVERSE(seq) CAT(EVAL2(REVERSE_A ZIP_(seq, seq)), _END)

#define ZIP(seq, seq2) ZIP_(REVERSE(seq), seq2)

#define GEN_U_A(...) U DELAY_OPEN_BRACE_1() GEN_U_B
#define GEN_U_B(...) U DELAY_OPEN_BRACE_1() GEN_U_A
#define GEN_U_A_END
#define GEN_U_B_END
#define GEN_U(seq) CAT(GEN_U_A seq, _END)

#define GEN_BRACE_1_A(...) ( GEN_BRACE_1_B
#define GEN_BRACE_1_B(...) ( GEN_BRACE_1_A
#define GEN_BRACE_1_A_END
#define GEN_BRACE_1_B_END
#define GEN_BRACE_1(seq) CAT___(GEN_BRACE_1_A seq, _END)

#define GEN_BRACE_2_A(...) ) GEN_BRACE_2_B
#define GEN_BRACE_2_B(...) ) GEN_BRACE_2_A
#define GEN_BRACE_2_A_END
#define GEN_BRACE_2_B_END
#define GEN_BRACE_2(seq) CAT__(EVAL2(GEN_BRACE_2_A seq), _END)

#define U_(...) __VA_ARGS__

#define U(...) U_ __VA_ARGS__

#define TEST_BRACE_2(...) 0, VOID DELAY_OPEN_BRACE_2()

#define EQUAL_LENGTH_(seq, seq2) \
  EVAL2(IF_ELSE(TEST_BRACE_2 EVAL2(GEN_U(seq) GEN_BRACE_1_A seq2 YES GEN_BRACE_2_A seq2 GEN_BRACE_2_A seq), DELAY_CLOSE_BRACE_2() NO, YES))

#define AND_YES_YES YES
#define AND_YES_NO NO
#define AND_NO_YES NO
#define AND_NO_NO NO

#define EQUAL_LENGTH(seq, seq2) CAT(AND_, CAT(EQUAL_LENGTH_(seq, seq2), CAT(_, EQUAL_LENGTH_(seq2, seq))))

#define MULTIPLY_2(seq) seq seq

#define GEN_MULTIPLY_2_A(...) MULTIPLY_2 DELAY_OPEN_BRACE_1() GEN_MULTIPLY_2_B
#define GEN_MULTIPLY_2_B(...) MULTIPLY_2 DELAY_OPEN_BRACE_1() GEN_MULTIPLY_2_A
#define GEN_MULTIPLY_2_A_END
#define GEN_MULTIPLY_2_B_END
#define GEN_MULTIPLY(seq) CAT(GEN_MULTIPLY_2_A seq, _END)

#define EXPONENTIAL(seq) CAT(GEN_MULTIPLY(seq)(~) GEN_BRACE_2_A seq, _END)

// EQUAL_LENGTH((a)(), (c)(d))  // YES
// SLIDE_2((a)(b)(c)) // (a, b)(b, c)
// SLIDE_3((a)(b)(c)(d)(e)(f)) // (a, b, c)(b, c, d)(c, d, e)(d, e, f)
// ZIP((a)(b)(c), (d)(e)(f))  // (a, d)(b, e)(c, f)

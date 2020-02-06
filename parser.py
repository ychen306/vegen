import ply.yacc as yacc

from lex import tokens
from sema_ast import *

def new_binary_expr(parser, op, a, b):
  expr_id = gen_unique_id(parser)
  expr = BinaryExpr(op, a, b, expr_id)
  parser.binary_exprs.append(expr)
  return expr

def parse_binary(op, p):
  p[0] = new_binary_expr(p.parser, op, p[1], p[3])

def parse_unary(op, p):
  p[0] = UnaryExpr(op, p[2])

if __name__ != '__main__':
  def p_error(p):
    raise SyntaxError('Parser error')

def p_stmts(p):
  '''stmts : stmt
           | stmts stmt
  '''
  if len(p) == 2:
    p[0] = [p[1]]
  else:
    p[0] = p[1] + [p[2]]

def p_func_decl(p):
  '''stmt : DEFINE ID LPAREN args RPAREN LBRACKET stmts RBRACKET
  '''
  p[0] = FuncDef(p[2], p[4], p[7])

def p_stmt_break(p):
  'stmt : BREAK'
  p[0] = Break()

def p_stmt_expr(p):
  'stmt : expr'
  p[0] = p[1]

def p_match(p):
  '''stmt : CASE expr OF cases ESAC
  '''
  p[0] = Match(p[2], p[4])

def p_single_case(p):
  '''cases : CASE_HEADER stmts
           | cases CASE_HEADER stmts
  '''
  if len(p) == 3:
    p[0] = [Case(p[1], p[2])]
  else:
    p[0] = p[1] + [Case(p[2], p[3])]

def p_return(p):
  'stmt : RETURN expr'
  p[0] = Return(p[2])

def p_expr_assign(p):
  'expr : expr UPDATE expr'
  p[0] = Update(p[1], p[3])

def p_expr_assign_op(p):
  'expr : OP UPDATE ID'
  p[0] = OpUpdate(p[3])

def p_expr_plus_equal(p):
  'expr : expr PLUS_EQUAL expr'
  p[0] = Update(p[1], new_binary_expr(p.parser, op='+', a=p[1], b=p[3]))

def p_expr_or_equal(p):
  'expr : expr OR_EQUAL expr'
  p[0] = Update(p[1], new_binary_expr(p.parser, op='|', a=p[1], b=p[3]))

def p_stmt_while(p):
  'stmt : DO WHILE expr stmts OD'
  p[0] = While(p[3], p[4])

def p_stmt_for(p):
  'stmt : FOR ID UPDATE expr TO expr stmts ENDFOR'
  p[0] = For(p[2], p[4], p[6], p[7], True)

def p_stmt_for_dec(p):
  'stmt : FOR ID UPDATE expr DOWNTO expr stmts ENDFOR'
  p[0] = For(p[2], p[4], p[6], p[7], False)

def p_stmt_if(p):
  'stmt : IF expr THEN stmts FI'
  p[0] = If(p[2], p[4], [])

def p_stmt_if2(p):
  'stmt : IF expr THEN stmts ELSE stmts FI'
  p[0] = If(p[2], p[4], p[6])

def p_stmt_if_no_then(p):
  'stmt : IF expr stmts FI'
  p[0] = If(p[2], p[3], [])

def p_stmt_if2_no_then(p):
  'stmt : IF expr stmts ELSE stmts FI'
  p[0] = If(p[2], p[3], p[5])

def p_stmt_if2_no_then_no_fi(p):
  'stmt : IF expr stmts ELSE stmts'
  p[0] = If(p[2], p[3], p[5])

def p_stmt_pseudo(p):
  'stmt : PSEUDO'
  p[0] = PseudoStmt(p[1])

def p_expr_call(p):
  'expr : ID LPAREN args RPAREN'
  p[0] = Call(p[1], p[3])

def p_expr_call_no_args(p):
  'expr : ID LPAREN RPAREN'
  p[0] = Call(p[1], [])

def p_expr_reg_sel(p):
  'expr : ID LBRACKET expr RBRACKET'
  p[0] = RegSel(p[1], p[3])

def p_expr_lookup(p):
  'expr : expr DOT ID'
  p[0] = Lookup(p[1], p[3])

def p_args(p):
  '''args : expr
        | args COMMA expr
  '''
  if len(p) == 2:
    p[0] = [p[1]]
  else:
    p[0] = p[1] + [p[3]]

def p_expr_bit_index(p):
  'expr : expr LBRACE expr RBRACE'
  p[0] = BitSlice(p[1], lo=p[3], hi=p[3])

def p_expr_bit_slice(p):
  'expr : expr LBRACE expr COLON expr RBRACE'
  p[0] = BitSlice(p[1], p[3], p[5])

def p_expr_select(p):
  'expr : expr QUEST expr COLON expr'
  p[0] = Select(p[1], p[3], p[5])

def p_expr_not(p):
  'expr : NOT expr'
  parse_unary('NOT', p)

def p_expr_neg(p):
  'expr : MINUS expr %prec NEG'
  parse_unary('-', p)

def p_expr_bitwise_not(p):
  'expr : BITWISE_NOT expr'
  parse_unary('~', p)

def p_expr_bitwise_and(p):
  'expr : expr BITWISE_AND expr'
  parse_binary('&', p)

def p_expr_bitwise_or(p):
  'expr : expr BITWISE_OR expr'
  parse_binary('|', p)

def p_indirect_binary_op(p):
  'expr : expr OP expr'
  parse_binary(p[2], p)

def p_expr_plus(p):
  'expr : expr PLUS expr'
  parse_binary('+', p)

def p_expr_minus(p):
  'expr : expr MINUS expr'
  parse_binary('-', p)

def p_expr_times(p):
  'expr : expr TIMES expr'
  parse_binary('*', p)

def p_expr_div(p):
  'expr : expr DIV expr'
  parse_binary('/', p)

def p_expr_mod(p):
  'expr : expr MOD expr'
  parse_binary('%', p)

def p_expr_and(p):
  'expr : expr AND expr'
  parse_binary('AND', p)

def p_expr_or(p):
  'expr : expr OR expr'
  parse_binary('OR', p)

def p_expr_lshift(p):
  'expr : expr LSHIFT expr'
  parse_binary('<<', p)

def p_expr_rshift(p):
  'expr : expr RSHIFT expr'
  parse_binary('>>', p)

def p_expr_lshift_logical(p):
  'expr : expr LSHIFT_LOGICAL expr'
  parse_binary('<<<', p)

def p_expr_rshift_logical(p):
  'expr : expr RSHIFT_LOGICAL expr'
  parse_binary('>>>', p)

def p_expr_greater(p):
  'expr : expr GREATER expr'
  parse_binary('>', p)

def p_expr_less(p):
  'expr : expr LESS expr'
  parse_binary('<', p)

def p_expr_less_equal(p):
  'expr : expr LESS_EQUAL expr'
  parse_binary('<=', p)

def p_expr_greater_equal(p):
  'expr : expr GREATER_EQUAL expr'
  parse_binary('>=', p)

def p_expr_equal(p):
  'expr : expr EQUAL expr'
  parse_binary('==', p)

def p_expr_not_equal(p):
  'expr : expr NOT_EQUAL expr'
  parse_binary('!=', p)

def p_expr_xor(p):
  'expr : expr XOR expr'
  parse_binary('XOR', p)

def p_expr_wrapped(p):
  '''expr : LPAREN expr RPAREN
  '''
  p[0] = p[2]

def p_expr_var(p):
  'expr : ID'
  p[0] = Var(p[1])

def p_expr_num(p):
  'expr : NUMBER'
  p[0] = Number(p[1])

def p_expr_pseudo(p):
  'expr : PSEUDO'
  p[0] = PseudoExpr(p[1])

# in increasing order
precedence = (
    ('left', 'BITWISE_OR'),
    ('left', 'BITWISE_AND'),
    ('left', 'OR'),
    ('left', 'AND'),
    ('left', 'XOR'),
    ('left', 'EQUAL', 'NOT_EQUAL'),
    ('left', 'GREATER', 'LESS', 'GREATER_EQUAL', 'LESS_EQUAL'),
    ('left', 'LSHIFT', 'RSHIFT', 'LSHIFT_LOGICAL', 'RSHIFT_LOGICAL'),
    ('left', 'PLUS', 'MINUS'),
    ('left', 'TIMES', 'DIV', 'MOD'),
    ('right', 'NOT', 'NEG', 'BITWISE_NOT'),
    ('left', 'DOT', 'LPAREN', 'RPAREN', 'LBRACE', 'RBRACE'),
)

parser = yacc.yacc()

def gen_unique_id(parser):
  parser.id_counter += 1
  return parser.id_counter

def reset_parser_state(parser):
  parser.id_counter = 0
  parser.binary_exprs = []

def parse(src):
  reset_parser_state(parser)
  ast = parser.parse(src)
  binary_exprs = parser.binary_exprs
  reset_parser_state

  return ast, binary_exprs

if __name__ == '__main__':
  # from https://www.felixcloutier.com/x86/vpgatherdq:vpgatherqq
  from pprint import pprint
  test = '''
      MASK[MAXVL-1:128] ← 0;
FOR j←0 to 3
    i←j * 32;
    IF MASK[31+i] THEN
        MASK[i +31:i]←FFFFFFFFH; // extend from most significant bit
    ELSE
        MASK[i +31:i]←0;
    FI;
ENDFOR

FOR j←0 to 3
    i←j * 32;
    DATA_ADDR←BASE_ADDR + SignExtend(VINDEX[i+31:i])*SCALE + DISP;
    IF MASK[31+i] THEN
        DEST[i +31:i]←FETCH_32BITS(DATA_ADDR); // a fault exits the instruction
    FI;
    MASK[i +31:i]←0;
ENDFOR
DEST[MAXVL-1:128] ← 0;
'''

  test2 = '''
  FOR l←0 TO VL-1 // with increments of 128
    temp1[255:0] ← ((SRC1[l+127:l] << 128) OR SRC2[l+127:l])>>(imm8[7:0]*8);
    TMP_DEST[l+127:l] ← temp1[127:0]
ENDFOR;
FOR j←0 TO KL-1
    i←j * 8
    IF k1[j] OR *no writemask*
        THEN DEST[i+7:i]←TMP_DEST[i+7:i]
        ELSE
            IF *merging-masking*
                        ; merging-masking
                THEN *DEST[i+7:i] remains unchanged*
                ELSE *zeroing-masking*
                            ; zeroing-masking
                    DEST[i+7:i] = 0
            FI
    FI;
ENDFOR;
DEST[MAXVL-1:VL] ← 0
  '''

  test3 = '''
    //IF SRC1[31:0] > SRC2[31:0]
    //THEN DEST[31:0]←FFFFFFFFH;
    //ELSE DEST[31:0]←0; FI;

    IF SRC1[127:96] > SRC2[127:96]
    THEN
    DEST[127:96]←FFFFFFFFH
    ELSE DEST[127:96]←0; FI;

  '''

  test4 = '''
  FOR j := 0 to 1 i := j*128 tmp[255:0] := ((a[i+127:i] << 128) OR b[i+127:i]) >> (count[7:0]*8) dst[i+127:i] := tmp[127:0] ENDFOR dst[MAX:256] := 0
  '''

  test5 = '''
  a = b.c[4]
  '''

  test6 = '''
  DEFINE INTERLEAVE_HIGH_BYTES(src1[63:0], src2[63:0]) {
      dst[7:0] := src1[39:32]
      dst[15:8] := src2[39:32]
      dst[23:16] := src1[47:40]
      dst[31:24] := src2[47:40]
      dst[39:32] := src1[55:48]
      dst[47:40] := src2[55:48]
      dst[55:48] := src1[63:56]
      dst[63:56] := src2[63:56]
      RETURN dst[63:0]
      }
dst[63:0] := INTERLEAVE_HIGH_BYTES(a[63:0], b[63:0])
  '''

  test7 = '''
  FOR j := 0 to 1
	i := j*32
	dst[i+31:i] := a[i+31:i+16]*b[i+31:i+16] + a[i+15:i]*b[i+15:i]
ENDFOR
  '''

  test8 = '''
  FOR j := 0 to 3
	i := j*16
	IF count[63:0] > 15
		dst[i+15:i] := 0
	ELSE
		dst[i+15:i] := ZeroExtend(a[i+15:i] << count[63:0])
	FI
ENDFOR
  '''

  test9 = '''
  dst[63:0] := ((NOT a[63:0]) AND b[63:0])
  '''

  test10 = '''
  FOR j := 0 to 7
	i := j*8
	dst[i+7:i] := ( a[i+7:i] == b[i+7:i] ) ? 0xFF : 0
ENDFOR
  '''

  test11 = '''
  DEFINE SELECT4(src, control) {
	CASE(control[1:0]) OF
	0:	tmp[15:0] := src[15:0]
	1:	tmp[15:0] := src[31:16]
	2:	tmp[15:0] := src[47:32]
	3:	tmp[15:0] := src[63:48]
	ESAC
	RETURN tmp[15:0]
}
dst[15:0] := SELECT4(a[63:0], imm8[1:0])
dst[31:16] := SELECT4(a[63:0], imm8[3:2])
dst[47:32] := SELECT4(a[63:0], imm8[5:4])
dst[63:48] := SELECT4(a[63:0], imm8[7:6])
  '''

  test12 = '''
  dst[31:0] := APPROXIMATE(1.0/a[31:0])
dst[127:32] := a[127:32]
  '''

  test13 = '''
  dst[31:0] := ( a[31:0] <= b[31:0] ) ? 0xffffffff : 0
dst[127:32] := a[127:32]
  '''

  test14 = '''
  dst[31:0] := ( a[31:0] != b[31:0] ) ? 0xffffffff : 0
dst[127:32] := a[127:32]
  '''

  test15 = '''
  dst[31:0] := (!( a[31:0] < b[31:0] )) ? 0xffffffff : 0
dst[127:32] := a[127:32]
  '''

  test16 = '''
  FOR j := 0 to 15
	i := j*8
	IF b[i+7:i] < 0
		dst[i+7:i] := -(a[i+7:i])
	ELSE IF b[i+7:i] == 0
		dst[i+7:i] := 0
	ELSE
		dst[i+7:i] := a[i+7:i]
	FI
ENDFOR
  '''

  test17 = '''
  IF (a[127:0] AND b[127:0] == 0)
	ZF := 1
ELSE
	ZF := 0
FI
IF ((NOT a[127:0]) AND b[127:0] == 0)
	CF := 1
ELSE
	CF := 0
FI
IF (ZF == 0 && CF == 0)
	dst := 1
ELSE
	dst := 0
FI
  '''

  test18 = '''
  size := (imm8[0] ? 16 : 8) // 8 or 16-bit characters
UpperBound := (128 / size) - 1
bInvalid := 0
FOR j := 0 to UpperBound
	n := j*size
	IF b[n+size-1:n] == 0
		bInvalid := 1
	FI
ENDFOR
dst := bInvalid
  '''

  test19 = '''
  CASE (imm8[7:0]) OF
0: OP := _CMP_EQ_OQ
1: OP := _CMP_LT_OS
2: OP := _CMP_LE_OS
3: OP := _CMP_UNORD_Q
4: OP := _CMP_NEQ_UQ
5: OP := _CMP_NLT_US
6: OP := _CMP_NLE_US
7: OP := _CMP_ORD_Q
8: OP := _CMP_EQ_UQ
9: OP := _CMP_NGE_US
10: OP := _CMP_NGT_US
11: OP := _CMP_FALSE_OQ
12: OP := _CMP_NEQ_OQ
13: OP := _CMP_GE_OS
14: OP := _CMP_GT_OS
15: OP := _CMP_TRUE_UQ
16: OP := _CMP_EQ_OS
17: OP := _CMP_LT_OQ
18: OP := _CMP_LE_OQ
19: OP := _CMP_UNORD_S
20: OP := _CMP_NEQ_US
21: OP := _CMP_NLT_UQ
22: OP := _CMP_NLE_UQ
23: OP := _CMP_ORD_S
24: OP := _CMP_EQ_US
25: OP := _CMP_NGE_UQ
26: OP := _CMP_NGT_UQ
27: OP := _CMP_FALSE_OS
28: OP := _CMP_NEQ_OS
29: OP := _CMP_GE_OQ
30: OP := _CMP_GT_OQ
31: OP := _CMP_TRUE_US
ESAC
FOR j := 0 to 1
	i := j*64
	dst[i+63:i] := ( a[i+63:i] OP b[i+63:i] ) ? 0xFFFFFFFFFFFFFFFF : 0
ENDFOR
dst[MAX:128] := 0
  '''

  test20 = '''
  IF (b[1] == 0) dst[63:0] := a[63:0]; FI
//IF (b[1] == 1) dst[63:0] := a[127:64]; FI
//IF (b[65] == 0) dst[127:64] := a[63:0]; FI
//IF (b[65] == 1) dst[127:64] := a[127:64]; FI
//IF (b[129] == 0) dst[191:128] := a[191:128]; FI
//IF (b[129] == 1) dst[191:128] := a[255:192]; FI
//IF (b[193] == 0) dst[255:192] := a[191:128]; FI
//IF (b[193] == 1) dst[255:192] := a[255:192]; FI
//dst[MAX:256] := 0
  '''

  test21 = '''
  CASE 0 OF
0: // individual-address invalidation retaining global translations
	OP_PCID := descriptor[11:0]
	ADDR := descriptor[127:64]
	BREAK
//1: // single PCID invalidation retaining globals
//	OP_PCID := descriptor[11:0]
//	// invalidate all mappings tagged with OP_PCID except global translations
//	BREAK
//2: // all PCID invalidation
//	// invalidate all mappings tagged with any PCID
//	BREAK
//3: // all PCID invalidation retaining global translations
//	// invalidate all mappings tagged with any PCID except global translations
//	BREAK
ESAC
  '''

  test22 = '''
 ProcessorState[x87_FPU] := mem_addr.FPUSSESave_Area[FPU]

  st_mask := mem_addr.HEADER.XSTATE_BV[62:0]
FOR i := 0 to 62
	IF (rs_mask[i] AND XCR0[i])
		IF st_mask[i]
			CASE (i) OF
			0: ProcessorState[x87_FPU] := mem_addr.FPUSSESave_Area[FPU]
			1: ProcessorState[SSE] := mem_addr.FPUSSESaveArea[SSE]
			DEFAULT: ProcessorState[i] := mem_addr.Ext_Save_Area[i]
			ESAC
		ELSE
			// ProcessorExtendedState := Processor Supplied Values
			CASE (i) OF
			1: MXCSR := mem_addr.FPUSSESave_Area[SSE]
			ESAC
		FI
	FI
	i := i + 1
ENDFOR
  '''

  test23 = '''
  DEFINE gf2p8mul_byte(src1byte, src2byte) {
	tword := 0
	FOR i := 0 to 7
		IF src2byte.bit[i]
			tword := tword XOR (src1byte << i)
		FI
	ENDFOR
	FOR i := 14 downto 8
		p := 0x11B << (i-8)
		IF tword.bit[i]
			tword := tword XOR p
		FI
	ENDFOR
	RETURN tword.byte[0]
}
FOR j := 0 TO 63
	IF k[j]
		dst.byte[j] := gf2p8mul_byte(a.byte[j], b.byte[j])
	ELSE
		dst.byte[j] := 0
	FI
ENDFOR
dst[MAX:512] := 0
  '''

  test24 = '''
  FOR j := 0 to 7
	i := j*64
	IF k[j]
		dst[i+63:i] := concat(b[i+63:i], a[i+63:i]) >> (c[i+63:i] & 63)
	ELSE
		dst[i+63:i] := 0
	FI
ENDFOR
dst[MAX:512] := 0
  '''

  test25 = '''
  DEFINE ReduceArgumentPS(src1[31:0], imm8[7:0])
{
	IF src1[31:0] == NAN
		RETURN (src1[31:0] := QNaN)
	FI

	m := imm8[7:4] // number of fraction bits after the binary point to be preserved
	rc := imm8[1:0] // round control
	rc_src := imm8[2] // round ccontrol source
	spe := 0
	tmp[31:0] := pow(2, -m)*ROUND(pow(2, m)*src1[31:0], spe, rc_source, rc)
	tmp[31:0] := src1[31:0] - tmp[31:0]
	RETURN tmp[31:0]
}
FOR j := 0 to 7
	i := j*32
	IF k[j]
		dst[i+31:i] := ReduceArgumentPS(a[i+31:i], imm8[7:0])
	ELSE
		dst[i+31:i] := src[i+31:i]
	FI
ENDFOR
dst[MAX:256] := 0
  '''

  test26 = '''
  size := (imm8[0] ? 16 : 8) // 8 or 16-bit characters
UpperBound := (128 / size) - 1
// compare all characters
aInvalid := 0
bInvalid := 0
FOR i := 0 to UpperBound
	m := i*size
	FOR j := 0 to UpperBound
		n := j*size
		BoolRes[i][j] := (a[m+size-1:m] == b[n+size-1:n])

		// invalidate characters after EOS
		IF a[m+size-1:m] == 0
			aInvalid := 1
		FI
		IF b[n+size-1:n] == 0
			bInvalid := 1
		FI

		// override comparisons for invalid characters
		CASE (imm8[3:2]) OF
		0:  // equal any
			IF (!aInvalid && bInvalid)
				BoolRes[i][j] := 0
			ELSE IF (aInvalid && !bInvalid)
				BoolRes[i][j] := 0
			ELSE IF (aInvalid && bInvalid)
				BoolRes[i][j] := 0
			FI
		1:  // ranges
			IF (!aInvalid && bInvalid)
				BoolRes[i][j] := 0
			ELSE IF (aInvalid && !bInvalid)
				BoolRes[i][j] := 0
			ELSE IF (aInvalid && bInvalid)
				BoolRes[i][j] := 0
			FI
		2:  // equal each
			IF (!aInvalid && bInvalid)
				BoolRes[i][j] := 0
			ELSE IF (aInvalid && !bInvalid)
				BoolRes[i][j] := 0
			ELSE IF (aInvalid && bInvalid)
				BoolRes[i][j] := 1
			FI
		3:  // equal ordered
			IF (!aInvalid && bInvalid)
				BoolRes[i][j] := 0
			ELSE IF (aInvalid && !bInvalid)
				BoolRes[i][j] := 1
			ELSE IF (aInvalid && bInvalid)
				BoolRes[i][j] := 1
			FI
		ESAC
	ENDFOR
ENDFOR
// aggregate results
CASE (imm8[3:2]) OF
0:  // equal any
	IntRes1 := 0
	FOR i := 0 to UpperBound
		FOR j := 0 to UpperBound
			IntRes1[i] := IntRes1[i] OR BoolRes[i][j]
		ENDFOR
	ENDFOR
1:  // ranges
	IntRes1 := 0
	FOR i := 0 to UpperBound
		FOR j := 0 to UpperBound, j += 2
			IntRes1[i] := IntRes1[i] OR (BoolRes[i][j] AND BoolRes[i][j+1])
		ENDFOR
	ENDFOR
2:  // equal each
	IntRes1 := 0
	FOR i := 0 to UpperBound
		IntRes1[i] := BoolRes[i][i]
	ENDFOR
3:  // equal ordered
	IntRes1 := (imm8[0] ? 0xFF : 0xFFFF)
	FOR i := 0 to UpperBound
		k := i
		FOR j := 0 to UpperBound-i
			IntRes1[i] := IntRes1[i] AND BoolRes[k][j]
			k := k+1
		ENDFOR
	ENDFOR
ESAC
// optionally negate results
bInvalid := 0
FOR i := 0 to UpperBound
	IF imm8[4]
		IF imm8[5] // only negate valid
			IF b[n+size-1:n] == 0
				bInvalid := 1
			FI
			IF bInvalid // invalid, don't negate
				IntRes2[i] := IntRes1[i]
			ELSE // valid, negate
				IntRes2[i] := -1 XOR IntRes1[i]
			FI
		ELSE // negate all
			IntRes2[i] := -1 XOR IntRes1[i]
		FI
	ELSE // don't negate
		IntRes2[i] := IntRes1[i]
	FI
ENDFOR
// output
IF imm8[6] // byte / word mask
	FOR i := 0 to UpperBound
		j := i*size
		IF IntRes2[i]
			dst[j+size-1:j] := (imm8[0] ? 0xFF : 0xFFFF)
		ELSE
			dst[j+size-1:j] := 0
		FI
	ENDFOR
ELSE // bit mask
	dst[UpperBound:0] := IntRes2[UpperBound:0]
	dst[127:UpperBound+1] := 0
FI

  '''

  test = test26

  from lex import lexer
  lexer.input(test)
  for token in iter(lexer.token, None):
    print(token.type, token.value)

  print(test)
  parsed = parser.parse(test)
  pprint(parsed)

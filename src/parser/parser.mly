/* tokens that actually carry some payload */
%token <Rational.t> RATIONAL
%token <int> INT
%token <bool> BOOL
%token <Name.t> NAME

/* end of input token */
%token EOI

/* brackets and whatnot */
%token LEFT_PAREN
%token RIGHT_PAREN
%token LEFT_BRACKET
%token RIGHT_BRACKET

/* arithmetic symbols */
%token PLUS MULT DIV
%left PLUS MULT DIV

/* boolean symbols */
/* comparison operators */
%token EQ LT GT LEQ GEQ NEQ
%left EQ LT GT LEQ GEQ NEQ

/* logical operators */
%token AND OR NOT
%left AND OR

/* assignments and some control flow */
%token ASSIGN DRAW COMMA
%token WHILE IF THEN ELSE DO

/* entry */
%start <AST.expr> prog
%%

/* the rules */

/* prog is our entry */
prog:
  | e = expr; EOI {e}

expr:
  /* parens are fine, and possible useful to enforce precedence */
  | LEFT_PAREN; e = expr; RIGHT_PAREN {e}

  /* literals */
  | q = INT {AST.Literal( AST.Rational (Rational.Q (q, 1)))}
  | b = BOOL {AST.Literal (AST.Boolean b)}

  /* binary and unary ops --- need to be defined in the inlines below */
  | l = expr; o = binaryop; r = expr {AST.BinaryOp (o, l, r)}
  | o = unaryop; e = expr {AST.UnaryOp (o, e)}

  /* function calls */
  | f = NAME; LEFT_PAREN; es = separated_list(COMMA, expr); RIGHT_PAREN {AST.FunCall (f, es)}

  /* identifiers */
  | i = identifier {AST.Identifier i}

identifier:
  | n = NAME {AST.Var n}
  | n = NAME; LEFT_BRACKET; i = expr; RIGHT_BRACKET {AST.IndexedVar (n, i)}

%inline binaryop:
  | PLUS {Operation.of_string "PLUS"}
  | MULT {Operation.of_string "MULT"}
  | DIV {Operation.of_string "DIV"}
  | AND {Operation.of_string "AND"}
  | OR {Operation.of_string "OR"}
  | EQ {Operation.of_string "EQ"}
  | NEQ {Operation.of_string"NEQ"}
  | LT {Operation.of_string "LT"}
  | GT {Operation.of_string "GT"}
  | LEQ {Operation.of_string "LEQ"}
  | GEQ {Operation.of_string "GEQ"}

%inline unaryop:
  | NOT {Operation.of_string "NOT"}
/* tokens that actually carry some payload */
%token <Rational.t> RATIONAL
%token <int> INT
%token <bool> BOOL
%token <Name.t> NAME

/* end of input token */
%token EOI

/* logical tokens */
%token AND OR NOT


/* brackets and whatnot */
%token LEFT_PAREN RIGHT_PAREN
%token LEFT_BRACKET RIGHT_BRACKET
%token LEFT_BRACE RIGHT_BRACE

/* arithmetic symbols */
%token PLUS MULT DIV MINUS


/* boolean symbols */
/* comparison operators */
%token EQ LT GT LEQ GEQ NEQ

/* assignments and some control flow */
%token SEMICOLON EOL
%token ASSIGN DRAW COMMA
%token WHILE IF THEN ELSE DO

/* entry */
%start <AST.t> program
%%

/* version 2.0 */
program:
  | ss = list(statement); EOI { AST.Block ss }

statement:
  | e = assignment_statement {e}
  | e = if_statement {e}
  | e = while_statement {e}
  | e = block_statement {e}

assignment_statement:
  | x = identifier; ASSIGN; e = expression; SEMICOLON { AST.Assign (x, e) }
  | x = identifier; DRAW; e = expression; SEMICOLON { AST.Draw (x, e) }

if_statement:
  | IF; c = delimited(LEFT_PAREN, expression, RIGHT_PAREN); THEN; t = statement; ELSE; f = statement 
  { AST.ITE (c, t, f) }

while_statement:
  | WHILE; c = delimited(LEFT_PAREN, expression, RIGHT_PAREN); b = statement
  { AST.While (c, b) }

block_statement:
  | bs = delimited(LEFT_BRACE, list(statement), RIGHT_BRACE)
  { AST.Block bs }

expression:
  | e = unary { e }
  | l = unary; op = binary_op; r = expression { AST.BinaryOp (op, l, r) }

unary:
  | e = base { e }
  | op = unary_op; e = base { AST.UnaryOp (op, e) }

base:
  | c = literal {c}
  | x = identifier { AST.Identifier x }
  | f = identifier; args = plist(expression) { AST.FunCall (f, args) }
  | e = delimited(LEFT_PAREN, expression, RIGHT_PAREN) { e }

literal:
  | q = INT { AST.Literal (AST.Rational (Rational.Q (q, 1))) }
  | b = BOOL { AST.Literal (AST.Boolean b) }

identifier:
  | n = NAME {AST.Var n}
  | n = NAME; LEFT_BRACKET; i = expression; RIGHT_BRACKET {AST.IndexedVar (n, i)}

/* the operations */
%inline unary_op:
  | NOT { Operation.of_string "Not" }
  | MINUS { Operation.of_string "Minus" }
%inline binary_op:
  | PLUS { Operation.of_string "Plus" }
  | MULT { Operation.of_string "Mult" }
  | DIV  { Operation.of_string "Div" }
  | MINUS { Operation.of_string "Minus" }
  | EQ { Operation.of_string "Eq" }
  | NEQ { Operation.of_string "NEq" }
  | LEQ { Operation.of_string "LEq" }
  | GEQ { Operation.of_string "GEq" }
  | LT { Operation.of_string "LT" }
  | GT { Operation.of_string "RT" }
  | AND { Operation.of_string "And" }
  | OR { Operation.of_string "Or" }

/* a simplifying macro for above */
%public plist(X):
  | xs = delimited(LEFT_PAREN, separated_list(COMMA, X), RIGHT_PAREN) { xs }

/* tokens that actually carry some payload */
/* %token <Rational.t> RATIONAL */
%token <int> INT
%token <bool> BOOL
%token <Name.t> NAME

/* end of input token */
%token EOI

/* logical tokens */
%token AND OR NOT IMPLIES


/* brackets and whatnot */
%token LEFT_PAREN RIGHT_PAREN
%token LEFT_BRACKET RIGHT_BRACKET
%token LEFT_BRACE RIGHT_BRACE
%token LEFT_DOUBLE_BRACE RIGHT_DOUBLE_BRACE

/* arithmetic symbols */
%token PLUS MULT DIV MINUS
%token RATPLUS RATMULT RATDIV RATMINUS


/* boolean symbols */
/* comparison operators */
%token EQ LT GT LEQ GEQ NEQ
%token RATLT RATGT RATLEQ RATGEQ

/* assignments and some control flow */
%token SEMICOLON PERIOD
%token ASSIGN DRAW COMMA
%token WHILE IF THEN ELSE IN
%nonassoc THEN
%nonassoc ELSE

/* for conditions */
%token EXISTS FORALL

/* entry */
%start <AST.program> program
%start <AST.expr> just_expression
%start <AST.id> just_identifier
%%

/* version 2.0 */
program:
  | pre = annotation; ss = list(statement); post = annotation; c = cost; EOI 
    { (pre, AST.Block ss, post, c) }

just_expression:
  | e = expression; EOI { e }

just_identifier:
  | e = identifier; EOI { e }

statement:
  | e = if_statement {e}
  | e = while_statement {e}
  | e = block_statement {e}
  | e = assignment_statement {e}

assignment_statement:
  | x = identifier; ASSIGN; e = expression; SEMICOLON { AST.Assign (x, e) }
  | x = identifier; DRAW; e = expression; SEMICOLON { AST.Draw (x, e) }

if_statement:
  | IF; c = delimited(LEFT_PAREN, expression, RIGHT_PAREN); THEN; t = statement; ELSE; f = statement
    { AST.ITE (c, t, f) }
  | IF; c = delimited(LEFT_PAREN, expression, RIGHT_PAREN); THEN; t = statement
    { AST.ITE (c, t, AST.Block []) }

while_statement:
  | WHILE; c = delimited(LEFT_PAREN, expression, RIGHT_PAREN); b = statement
  { AST.While (c, b) }

block_statement:
  | bs = delimited(LEFT_BRACE, list(statement), RIGHT_BRACE)
  { AST.Block bs }

expression:
  | e = unary { e }
  | l = unary; op = binary_op; r = expression { AST.FunCall (op, [l ; r]) }

unary:
  | e = base { e }
  | op = unary_op; e = base { AST.FunCall (op, [e]) }

base:
  | c = literal {c}
  | x = identifier { AST.Identifier x }
  | f = NAME; args = plist(expression) { AST.FunCall (f, args) }
  | e = delimited(LEFT_PAREN, expression, RIGHT_PAREN) { e }

literal:
  | i = INT { AST.Literal (AST.Integer i) }
  | b = BOOL { AST.Literal (AST.Boolean b) }

identifier:
  | n = NAME {AST.Var n}
  | n = NAME; LEFT_BRACKET; i = expression; RIGHT_BRACKET {AST.IndexedVar (n, i)}

/* the operations */
%inline unary_op:
  | NOT { Name.of_string "not" }
  | MINUS { Name.of_string "negative" }
  | RATMINUS {Name.of_string "ratNegative"}
%inline binary_op:
  | PLUS { Name.of_string "plus" }
  | MULT { Name.of_string "mult" }
  | DIV  { Name.of_string "div" }
  | MINUS { Name.of_string "minus" }
  | EQ { Name.of_string "eq" }
  | NEQ { Name.of_string "neq" }
  | LEQ { Name.of_string "leq" }
  | GEQ { Name.of_string "geq" }
  | LT { Name.of_string "lt" }
  | GT { Name.of_string "gt" }
  | AND { Name.of_string "and" }
  | OR { Name.of_string "or" }
  | IMPLIES { Name.of_string "implies" }
  | RATPLUS { Name.of_string "ratPlus" }
  | RATMULT { Name.of_string "ratMult" }
  | RATDIV { Name.of_string "ratDiv" }
  | RATMINUS { Name.of_string "ratMinus" }
  | RATLEQ { Name.of_string "ratLeq" }
  | RATGEQ { Name.of_string "ratGeq" }
  | RATLT { Name.of_string "ratLt" }
  | RATGT { Name.of_string "ratGt" }

/* a simplifying macro for above */
%public plist(X):
  | xs = delimited(LEFT_PAREN, separated_list(COMMA, X), RIGHT_PAREN) { xs }

/* extension 1: syntax for annotations */
annotation:
  | xs = delimited(LEFT_DOUBLE_BRACE, quantified_expression, RIGHT_DOUBLE_BRACE) { xs }

quantified_expression:
  | EXISTS; i = NAME; PERIOD e = expression 
    { AST.FunCall (Name.of_string "exists", [AST.Identifier (AST.Var i); e]) }
  | FORALL; i = NAME; IN; 
    LEFT_BRACKET; l = expression; COMMA; u = expression; RIGHT_BRACKET; 
    PERIOD; e = expression 
      { AST.FunCall (Name.of_string "forall", [AST.Identifier (AST.Var i); l; u; e]) }
  | e = expression { e }
  /* | q = quantifier; i = NAME; PERIOD; e = expression { match q with
    | AST.Exists -> AST.FunCall (Name.of_string "exists", [AST.Identifier (AST.Var i); e])
    | AST.ForAll -> AST.FunCall (Name.of_string "forall", [AST.Identifier (AST.Var i); e])}
  | e = expression { e }

%inline quantifier:
  | EXISTS { AST.Exists }
  | FORALL { AST.ForAll } */

/* extension 2: syntax for explicit costs */
cost:
  | xs = delimited(LEFT_DOUBLE_BRACE, expression, RIGHT_DOUBLE_BRACE) { xs }
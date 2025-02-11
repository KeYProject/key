parser grammar RustySchemaParser;

import RustyParser;

options { tokenVocab = RustySchemaLexer; }
blockExpr
   : LCURLYBRACE CONTEXT_START stmts? CONTEXT_END RCURLYBRACE # ContextBlockExpr
   | LCURLYBRACE stmts? RCURLYBRACE # StandardBlockExpr
   ;

expr
   : schemaVariable # SchemaVarExpression
   | EXPAND_FN_BODY LPAREN schemaVariable RPAREN # ExpandFnBody
   | FN_FRAME LPAREN schemaVariable COMMA blockExpr RPAREN # FnFrame
   | literalExpr # LiteralExpression
   | pathExpr # PathExpression
   | expr DOT pathExprSegment LPAREN callParams? RPAREN # MethodCallExpression
   | expr DOT identifier # FieldExpression
   | expr DOT tupleIndex # TupleIndexingExpression
   | expr DOT KW_AWAIT # AwaitExpression
   | expr LPAREN callParams? RPAREN # CallExpression
   | expr LPAREN callParams? RPAREN AT # FunctionBodyExpression
   | expr LSQUAREBRACKET expr RSQUAREBRACKET # IndexExpression
   | expr QUESTION # ErrorPropagationExpression
   | (AND | ANDAND) KW_MUT? expr # BorrowExpression
   | STAR expr # DereferenceExpression
   | (MINUS | NOT) expr # NegationExpression
   | expr KW_AS typeNoBounds # TypeCastExpression
   | expr (STAR | SLASH | PERCENT) expr # ArithmeticOrLogicalExpression
   | expr (PLUS | MINUS) expr # ArithmeticOrLogicalExpression
   | expr (shl | shr) expr # ArithmeticOrLogicalExpression
   | expr AND expr # ArithmeticOrLogicalExpression
   | expr CARET expr # ArithmeticOrLogicalExpression
   | expr OR expr # ArithmeticOrLogicalExpression
   | expr comparisonOperator expr # ComparisonExpression
   | expr ANDAND expr # LazyBooleanExpression
   | expr OROR expr # LazyBooleanExpression
   | expr DOTDOT expr? # RangeExpression
   | DOTDOT expr? # RangeExpression
   | DOTDOTEQ expr # RangeExpression
   | expr DOTDOTEQ expr # RangeExpression
   | expr EQ expr # AssignmentExpression
   | expr compoundAssignOperator expr # CompoundAssignmentExpression
   | KW_CONTINUE label? expr? # ContinueExpression
   | KW_BREAK label? expr? # BreakExpression
   | KW_RETURN expr? # ReturnExpression
   | LPAREN expr RPAREN # GroupedExpression
   | LSQUAREBRACKET arrayElements? RSQUAREBRACKET # ArrayExpression
   | LPAREN tupleElements? RPAREN # TupleExpression
   | structExpr # StructExpression_
   | enumerationVariantExpr # EnumerationVariantExpression_
   | closureExpr # ClosureExpression_
   | exprWithBlock # ExpressionWithBlock_
   | PANIC LPAREN RPAREN # EmptyPanic
   ;

stmt
   : SEMI
   | item
   | letStmt
   | exprStmt
   | schemaStmt
   ;

schemaStmt
   : schemaVariable
   ;

identifierPattern
   : KW_REF? KW_MUT? (identifier | schemaVariable) (AT pattern)?
   ;

schemaVariable
   : SCHEMA_IDENTIFIER
   ;

rangePatternBound
   : schemaVariable
   | CHAR_LITERAL
   | BYTE_LITERAL
   | MINUS? INTEGER_LITERAL
   // | MINUS? FLOAT_LITERAL
   | pathExpr
   ;

typeNoBounds
   : parenthesizedType
   | implTraitTypeOneBound
   | traitObjectTypeOneBound
   | typePath
   | tupleType
   | neverType
   | rawPointerType
   | referenceType
   | arrayType
   | sliceType
   | inferredType
   | qualifiedPathInType
   | bareFunctionType
   | typeOf
   | schemaVariable
   ;

ifExpr
   : KW_IF expr (thenBlock=blockExpr | thenSV=schemaVariable) (KW_ELSE (elseBlock=blockExpr | elseIf=ifExpr | elseSV=schemaVariable))?
   ;

ifLetExpr
  : KW_IF KW_LET (pattern | patternSV=schemaVariable) EQ expr (thenBlock=blockExpr | thenSV=schemaVariable) (KW_ELSE (elseBlock=blockExpr | elseIf=ifExpr | elseIfLet=ifLetExpr | elseSV=schemaVariable))?
  ;

typeOf
   : TYPE_OF LPAREN expr RPAREN
   ;

loopExpr
   : loopLabel? (infiniteLoopExpr
    | loopScope)
   ;

infiniteLoopExpr
   : 'loop' (block=blockExpr | sv=schemaVariable)
   ;

loopScope
    : 'loop_scope!' '(' idx=schemaVariable ',' blockExpr ')';

loopLabel
   : label COLON
   ;

label
    : LIFETIME_OR_LABEL | schemaVariable
    ;
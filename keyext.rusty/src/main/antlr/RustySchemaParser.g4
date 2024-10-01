parser grammar RustySchemaParser;

import RustyParser;

options { tokenVocab = RustySchemaLexer; }
blockExpr
   : '{' 'c#' stmts? '#c' '}' # ContextBlockExpr
   | '{' stmts? '}' # StandardBlockExpr
   ;

expr
   : schemaVariable # SchemaVarExpression
   | literalExpr # LiteralExpression
   | pathExpr # PathExpression
   | expr DOT pathExprSegment LPAREN callParams? RPAREN # MethodCallExpression
   | expr DOT identifier # FieldExpression
   | expr DOT tupleIndex # TupleIndexingExpression
   | expr DOT KW_AWAIT # AwaitExpression
   | expr LPAREN callParams? RPAREN # CallExpression
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
   | KW_CONTINUE LIFETIME_OR_LABEL? expr? # ContinueExpression
   | KW_BREAK LIFETIME_OR_LABEL? expr? # BreakExpression
   | KW_RETURN expr? # ReturnExpression
   | LPAREN expr RPAREN # GroupedExpression
   | LSQUAREBRACKET arrayElements? RSQUAREBRACKET # ArrayExpression
   | LPAREN tupleElements? RPAREN # TupleExpression
   | structExpr # StructExpression_
   | enumerationVariantExpr # EnumerationVariantExpression_
   | closureExpr # ClosureExpression_
   | exprWithBlock # ExpressionWithBlock_
   ;

stmt
   : ';'
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
   : 'if' expr (thenBlock=blockExpr | thenSV=schemaVariable) ('else' (elseBlock=blockExpr | elseIf=ifExpr | elseSV=schemaVariable))?
   ;

typeOf
   : TYPE_OF '(' expr ')'
   ;


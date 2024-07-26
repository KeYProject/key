parser grammar RustyWhileSchemaParser;

import RustyWhileParser;

options { tokenVocab = RustyWhileSchemaLexer; }

blockExpr
    : '{' 'c#' stmts? '#c' '}' # ContextBlockExpr
    | '{' stmts? '}'           # StandardBlockExpr
    ;

expr
   : literalExpr # LiteralExpression
   | pathExpr # PathExpression
   | expr '.' tupleIndex # TupleIndexingExpression
   | expr '(' callParams? ')' # CallExpression // 8.2.9
   | expr '[' expr ']' # IndexExpression // 8.2.6
   | expr 'as' type_ # TypeCastExpression // 8.2.4
   | expr ('*' | '/' | '%') expr # ArithmeticOrLogicalExpression // 8.2.4
   | expr ('+' | '-') expr # ArithmeticOrLogicalExpression // 8.2.4
   | expr '&' expr # ArithmeticOrLogicalExpression // 8.2.4
   | expr '^' expr # ArithmeticOrLogicalExpression // 8.2.4
   | expr '|' expr # ArithmeticOrLogicalExpression // 8.2.4
   | expr comparisonOperator expr # ComparisonExpression // 8.2.4
   | expr '&&' expr # LazyBooleanExpression // 8.2.4
   | expr '||' expr # LazyBooleanExpression // 8.2.4
   | expr '=' expr # AssignmentExpression // 8.2.4
   | 'return' expr? # ReturnExpression // 8.2.17
   | '(' expr ')' # GroupedExpression // 8.2.5
   | '[' arrayElements? ']' # ArrayExpression // 8.2.6
   | '(' tupleElements? ')' # TupleExpression // 8.2.7
   | exprWithBlock # ExpressionWithBlock_
   | schemaVariable # SchemaVarExpression
   ;

stmt
   : ';'
   | letStmt
   | exprStmt
   | schemaStmt
   ;

schemaStmt
    : schemaVariable
    ;

pattern
   : 'mut'? (identifier | schemaVariable)
   ;

schemaVariable
    : SCHEMA_IDENTIFIER
    ;
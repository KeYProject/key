parser grammar RustyWhileParser;


options { tokenVocab = RustyWhileLexer; }
@ header
{
    package org.key_project.rusty.parsing;
}
crate
   : item* EOF
   ;

item
   : visibility? function_
   ;

visibility
   : 'pub'
   ;

function_
   : 'fn' identifier '(' functionParams? ')' functionRetTy? blockExpr
   ;

functionParams
   : functionParam (',' functionParam)* ','?
   ;

functionParam
   : functionParamPattern
   ;

functionParamPattern
   : pattern ':' type_
   ;

functionRetTy
   : '->' type_
   ;

type_
   : parenthesizedType
   | typePath
   | tupleType
   | neverType
   | arrayType
   ;

parenthesizedType
   : '(' type_ ')'
   ;
   // 10.1.4
   
neverType
   : '!'
   ;
   // 10.1.5
   
tupleType
   : '(' ((type_ ',')+ type_?)? ')'
   ;
   // 10.1.6
   
arrayType
   : '[' type_ ';' expr ']'
   ;

typePath
   : '::'? typePathSegment ('::' typePathSegment)*
   ;

typePathSegment
   : pathIdentSegment '::'?
   ;

pathIdentSegment
   : identifier
   | 'super'
   | 'self'
   | 'crate'
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
   ;

comparisonOperator
   : '=='
   | '!='
   | '>'
   | '<'
   | '>='
   | '<='
   ;

literalExpr
   : CHAR_LITERAL
   | STRING_LITERAL
   | RAW_STRING_LITERAL
   | BYTE_LITERAL
   | BYTE_STRING_LITERAL
   | RAW_BYTE_STRING_LITERAL
   | INTEGER_LITERAL
   | KW_TRUE
   | KW_FALSE
   ;

exprWithBlock
   : blockExpr
   | loopExpr
   | ifExpr
   ;

pathExpr
   : '::'? pathExprSegment ('::' pathExprSegment)*
   ;

pathExprSegment
   : pathIdentSegment
   ;

blockExpr
   : '{' stmts? '}'
   ;

stmts
   : stmt+ expr?
   | expr
   ;

arrayElements
   : expr (',' expr)* ','?
   | expr ';' expr
   ;
   // 8.2.7
   
tupleElements
   : (expr ',')+ expr?
   ;

tupleIndex
   : INTEGER_LITERAL
   ;

callParams
   : expr (',' expr)* ','?
   ;

loopExpr
   : infiniteLoopExpr
   | predicateLoopExpr
   ;

infiniteLoopExpr
   : 'loop' blockExpr
   ;

predicateLoopExpr
   : 'while' expr /*except structExpression*/
   
   blockExpr
   ;

ifExpr
   : 'if' expr blockExpr ('else' (blockExpr | ifExpr))?
   ;

stmt
   : ';'
   | letStmt
   | exprStmt
   ;

letStmt
   : 'let' pattern (':' type_)? ('=' expr)? ';'
   ;

exprStmt
   : expr ';'
   | exprWithBlock ';'?
   ;

pattern
   : 'mut'? identifier
   ;

identifier
   : NON_KEYWORD_IDENTIFIER
   | RAW_IDENTIFIER
   ;


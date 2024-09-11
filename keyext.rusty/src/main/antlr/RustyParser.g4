parser grammar RustyParser;


options { tokenVocab = RustyLexer; }
@ header
{
package org.key_project.rusty.parsing;
}
crate
   : item* EOF
   ;

item
   : visibility? (module
   //| externCrate
   | useDeclaration | function_ | typeAlias | struct_ | enumeration | union_ | constantItem | staticItem | trait_ | implementation
   // | externBlock
   )
   ;

module
   : KW_UNSAFE? KW_MOD identifier (SEMI | LCURLYBRACE item* RCURLYBRACE)
   ;

useDeclaration
   : KW_USE useTree SEMI
   ;

useTree
   : (simplePath? PATHSEP)? (STAR | LCURLYBRACE (useTree (COMMA useTree)* COMMA?)? RCURLYBRACE)
   | simplePath (KW_AS (identifier | UNDERSCORE))?
   ;

visibility
   : 'pub'
   ;

function_
   : functionQualifiers KW_FN identifier genericParams? LPAREN functionParams? RPAREN functionRetTy? whereClause? (blockExpr | SEMI)
   ;

functionQualifiers
   : KW_CONST? // KW_ASYNC? KW_UNSAFE? (KW_EXTERN abi?)?
   
   ;

functionParams
   : selfParam COMMA?
   | (selfParam COMMA)? functionParam (COMMA functionParam)* COMMA?
   ;

selfParam
   : (shorthandSelf | typedSelf)
   ;

shorthandSelf
   : (AND lifetime?)? KW_MUT? KW_SELFVALUE
   ;

typedSelf
   : KW_MUT? KW_SELFVALUE COLON type_
   ;

functionParam
   : functionParamPattern
   | DOTDOTDOT
   | type_
   ;

functionParamPattern
   : pattern ':' type_
   ;

functionRetTy
   : '->' type_
   ;

typeAlias
   : KW_TYPE identifier genericParams? whereClause? (EQ type_)? SEMI
   ;

struct_
   : structStruct
   | tupleStruct
   ;

structStruct
   : KW_STRUCT identifier genericParams? whereClause? (LCURLYBRACE structFields? RCURLYBRACE | SEMI)
   ;

tupleStruct
   : KW_STRUCT identifier genericParams? LPAREN tupleFields? RPAREN whereClause? SEMI
   ;

structFields
   : structField (COMMA structField)* COMMA?
   ;

structField
   : visibility? identifier COLON type_
   ;

tupleFields
   : tupleField (COMMA tupleField)* COMMA?
   ;

tupleField
   : visibility? type_
   ;

enumeration
   : KW_ENUM identifier genericParams? whereClause? LCURLYBRACE enumItems? RCURLYBRACE
   ;

enumItems
   : enumItem (COMMA enumItem)* COMMA?
   ;

enumItem
   : visibility? identifier (enumItemTuple | enumItemStruct | enumItemDiscriminant)?
   ;

enumItemTuple
   : LPAREN tupleFields? RPAREN
   ;

enumItemStruct
   : LCURLYBRACE structFields? RCURLYBRACE
   ;

enumItemDiscriminant
   : EQ expr
   ;

union_
   : KW_UNION identifier genericParams? whereClause? LCURLYBRACE structFields RCURLYBRACE
   ;

constantItem
   : KW_CONST (identifier | UNDERSCORE) COLON type_ (EQ expr)? SEMI
   ;

staticItem
   : KW_STATIC KW_MUT? identifier COLON type_ (EQ expr)? SEMI
   ;

trait_
   : KW_TRAIT identifier genericParams? (COLON typeParamBounds?)? whereClause? LCURLYBRACE associatedItem* RCURLYBRACE
   ;

implementation
   : inherentImpl
   | traitImpl
   ;

inherentImpl
   : KW_IMPL genericParams? type_ whereClause? LCURLYBRACE associatedItem* RCURLYBRACE
   ;

traitImpl
   : KW_IMPL genericParams? NOT? typePath KW_FOR type_ whereClause? LCURLYBRACE associatedItem* RCURLYBRACE
   ;

genericParams
   : LT ((genericParam COMMA)* genericParam COMMA?)? GT
   ;

genericParam
   : (lifetimeParam | typeParam | constParam)
   ;

lifetimeParam
   : LIFETIME_OR_LABEL (COLON lifetimeBounds)?
   ;

typeParam
   : identifier (COLON typeParamBounds?)? (EQ type_)?
   ;

constParam
   : KW_CONST identifier COLON type_
   ;

whereClause
   : KW_WHERE (whereClauseItem COMMA)* whereClauseItem?
   ;

whereClauseItem
   : lifetimeWhereClauseItem
   | typeBoundWhereClauseItem
   ;

lifetimeWhereClauseItem
   : lifetime COLON lifetimeBounds
   ;

typeBoundWhereClauseItem
   : forLifetimes? type_ COLON typeParamBounds?
   ;

forLifetimes
   : KW_FOR genericParams
   ;

associatedItem
   : visibility? (typeAlias | constantItem | function_)
   ;

type_
   : typeNoBounds
   | implTraitType
   | traitObjectType
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
   ;

parenthesizedType
   : LPAREN type_ RPAREN
   ;

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

sliceType
   : LSQUAREBRACKET type_ RSQUAREBRACKET
   ;

referenceType
   : AND lifetime? KW_MUT? typeNoBounds
   ;

rawPointerType
   : STAR (KW_MUT | KW_CONST) typeNoBounds
   ;

bareFunctionType
   : forLifetimes? KW_FN LPAREN functionParametersMaybeNamedVariadic? RPAREN bareFunctionReturnType?
   ;

bareFunctionReturnType
   : RARROW typeNoBounds
   ;

functionParametersMaybeNamedVariadic
   : maybeNamedFunctionParameters
   | maybeNamedFunctionParametersVariadic
   ;

maybeNamedFunctionParameters
   : maybeNamedParam (COMMA maybeNamedParam)* COMMA?
   ;

maybeNamedParam
   : ((identifier | UNDERSCORE) COLON)? type_
   ;

maybeNamedFunctionParametersVariadic
   : (maybeNamedParam COMMA)* maybeNamedParam COMMA DOTDOTDOT
   ;

traitObjectType
   : KW_DYN? typeParamBounds
   ;

traitObjectTypeOneBound
   : KW_DYN? traitBound
   ;

implTraitType
   : KW_IMPL typeParamBounds
   ;

implTraitTypeOneBound
   : KW_IMPL traitBound
   ;

inferredType
   : UNDERSCORE
   ;

typeParamBounds
   : typeParamBound (PLUS typeParamBound)* PLUS?
   ;

typeParamBound
   : lifetime
   | traitBound
   ;

traitBound
   : QUESTION? forLifetimes? typePath
   | LPAREN QUESTION? forLifetimes? typePath RPAREN
   ;

lifetimeBounds
   : (lifetime PLUS)* lifetime?
   ;

lifetime
   : LIFETIME_OR_LABEL
   | KW_STATICLIFETIME
   | KW_UNDERLINELIFETIME
   ;

simplePath
   : PATHSEP? simplePathSegment (PATHSEP simplePathSegment)*
   ;

simplePathSegment
   : identifier
   | KW_SUPER
   | KW_SELFVALUE
   | KW_CRATE
   | KW_DOLLARCRATE
   ;

pathInExpr
   : PATHSEP? pathExprSegment (PATHSEP pathExprSegment)*
   ;

pathExprSegment
   : pathIdentSegment (PATHSEP genericArgs)?
   ;

pathIdentSegment
   : identifier
   | KW_SUPER
   | KW_SELFVALUE
   | KW_SELFTYPE
   | KW_CRATE
   | KW_DOLLARCRATE
   ;
   //TODO: let x : T<_>=something;
   
genericArgs
   : LT GT
   | LT genericArgsLifetimes (COMMA genericArgsTypes)? (COMMA genericArgsBindings)? COMMA? GT
   | LT genericArgsTypes (COMMA genericArgsBindings)? COMMA? GT
   | LT (genericArg COMMA)* genericArg COMMA? GT
   ;

genericArg
   : lifetime
   | type_
   | genericArgsConst
   | genericArgsBinding
   ;

genericArgsConst
   : blockExpr
   | MINUS? literalExpr
   | simplePathSegment
   ;

genericArgsLifetimes
   : lifetime (COMMA lifetime)*
   ;

genericArgsTypes
   : type_ (COMMA type_)*
   ;

genericArgsBindings
   : genericArgsBinding (COMMA genericArgsBinding)*
   ;

genericArgsBinding
   : identifier EQ type_
   ;

qualifiedPathInExpr
   : qualifiedPathType (PATHSEP pathExprSegment)+
   ;

qualifiedPathType
   : LT type_ (KW_AS typePath)? GT
   ;

qualifiedPathInType
   : qualifiedPathType (PATHSEP typePathSegment)+
   ;

typePath
   : PATHSEP? typePathSegment (PATHSEP typePathSegment)*
   ;

typePathSegment
   : pathIdentSegment PATHSEP? (genericArgs | typePathFn)?
   ;

typePathFn
   : LPAREN typePathInputs? RPAREN (RARROW type_)?
   ;

typePathInputs
   : type_ (COMMA type_)* COMMA?
   ;

expr
   : literalExpr # LiteralExpression
   | pathExpr # PathExpression
   | expr DOT pathExprSegment LPAREN callParams? RPAREN # MethodCallExpression
   | expr DOT identifier # FieldExpression
   | expr DOT tupleIndex # TupleIndexingExpression
   // | expr DOT KW_AWAIT                                          # AwaitExpression
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

comparisonOperator
   : '=='
   | '!='
   | '>'
   | '<'
   | '>='
   | '<='
   ;

shl
   : LT
   {_input.LA(1) == LT}? LT
   ;

shr
   : GT
   {_input.LA(1) == GT}? GT
   ;

compoundAssignOperator
   : PLUSEQ
   | MINUSEQ
   | STAREQ
   | SLASHEQ
   | PERCENTEQ
   | ANDEQ
   | OREQ
   | CARETEQ
   | SHLEQ
   | SHREQ
   ;

literalExpr
   : CHAR_LITERAL
   | STRING_LITERAL
   | RAW_STRING_LITERAL
   | BYTE_LITERAL
   | BYTE_STRING_LITERAL
   | RAW_BYTE_STRING_LITERAL
   | INTEGER_LITERAL
   // | FLOAT_LITERAL
   | KW_TRUE
   | KW_FALSE
   ;

exprWithBlock
   : blockExpr
   | loopExpr
   | ifExpr
   | ifLetExpr
   | matchExpr
   ;

pathExpr
   : pathInExpr
   | qualifiedPathInExpr
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

structExpr
   : structExprStruct
   | structExprTuple
   | structExprUnit
   ;

structExprStruct
   : pathInExpr LCURLYBRACE (structExprFields | structBase)? RCURLYBRACE
   ;

structExprFields
   : structExprField (COMMA structExprField)* (COMMA structBase | COMMA?)
   ;
   // outerAttribute here is not in doc
   
structExprField
   : (identifier | (identifier | tupleIndex) COLON expr)
   ;

structBase
   : DOTDOT expr
   ;

structExprTuple
   : pathInExpr LPAREN (expr (COMMA expr)* COMMA?)? RPAREN
   ;

structExprUnit
   : pathInExpr
   ;

enumerationVariantExpr
   : enumExprStruct
   | enumExprTuple
   | enumExprFieldless
   ;

enumExprStruct
   : pathInExpr LCURLYBRACE enumExprFields? RCURLYBRACE
   ;

enumExprFields
   : enumExprField (COMMA enumExprField)* COMMA?
   ;

enumExprField
   : identifier
   | (identifier | tupleIndex) COLON expr
   ;

enumExprTuple
   : pathInExpr LPAREN (expr (COMMA expr)* COMMA?)? RPAREN
   ;

enumExprFieldless
   : pathInExpr
   ;

callParams
   : expr (',' expr)* ','?
   ;

closureExpr
   : KW_MOVE? (OROR | OR closureParameters? OR) (expr | RARROW typeNoBounds blockExpr)
   ;

closureParameters
   : closureParam (COMMA closureParam)* COMMA?
   ;

closureParam
   : pattern (COLON type_)?
   ;

loopExpr
   : loopLabel? (infiniteLoopExpr | predicateLoopExpr | predicatePatternLoopExpr | iteratorLoopExpr)
   ;

infiniteLoopExpr
   : 'loop' blockExpr
   ;

predicateLoopExpr
   : 'while' expr /*except structExpression*/
   
   blockExpr
   ;

predicatePatternLoopExpr
   : KW_WHILE KW_LET pattern EQ expr blockExpr
   ;

iteratorLoopExpr
   : KW_FOR pattern KW_IN expr blockExpr
   ;

loopLabel
   : LIFETIME_OR_LABEL COLON
   ;

ifExpr
   : 'if' expr blockExpr ('else' (blockExpr | ifExpr))?
   ;

ifLetExpr
   : KW_IF KW_LET pattern EQ expr blockExpr (KW_ELSE (blockExpr | ifExpr | ifLetExpr))?
   ;

matchExpr
   : KW_MATCH expr LCURLYBRACE matchArms? RCURLYBRACE
   ;

matchArms
   : (matchArm FATARROW matchArmExpression)* matchArm FATARROW expr COMMA?
   ;

matchArmExpression
   : expr COMMA
   | exprWithBlock COMMA?
   ;

matchArm
   : pattern matchArmGuard?
   ;

matchArmGuard
   : KW_IF expr
   ;

stmt
   : ';'
   | item
   | letStmt
   | exprStmt
   ;

letStmt
   : 'let' patternNoTopAlt (':' type_)? ('=' expr)? ';'
   ;

exprStmt
   : expr ';'
   | exprWithBlock ';'?
   ;

pattern
   : OR? patternNoTopAlt (OR patternNoTopAlt)*
   ;

patternNoTopAlt
   : patternWithoutRange
   | rangePattern
   ;

patternWithoutRange
   : literalPattern
   | identifierPattern
   | wildcardPattern
   | restPattern
   | referencePattern
   | structPattern
   | tupleStructPattern
   | tuplePattern
   | groupedPattern
   | slicePattern
   | pathPattern
   ;

literalPattern
   : KW_TRUE
   | KW_FALSE
   | CHAR_LITERAL
   | BYTE_LITERAL
   | STRING_LITERAL
   | RAW_STRING_LITERAL
   | BYTE_STRING_LITERAL
   | RAW_BYTE_STRING_LITERAL
   | MINUS? INTEGER_LITERAL
   // | MINUS? FLOAT_LITERAL
   
   ;

identifierPattern
   : KW_REF? KW_MUT? identifier (AT pattern)?
   ;

wildcardPattern
   : UNDERSCORE
   ;

restPattern
   : DOTDOT
   ;

rangePattern
   : rangePatternBound DOTDOTEQ rangePatternBound # InclusiveRangePattern
   | rangePatternBound DOTDOT # HalfOpenRangePattern
   | rangePatternBound DOTDOTDOT rangePatternBound # ObsoleteRangePattern
   ;

rangePatternBound
   : CHAR_LITERAL
   | BYTE_LITERAL
   | MINUS? INTEGER_LITERAL
   // | MINUS? FLOAT_LITERAL
   | pathPattern
   ;

referencePattern
   : (AND | ANDAND) KW_MUT? patternWithoutRange
   ;

structPattern
   : pathInExpr LCURLYBRACE structPatternElements? RCURLYBRACE
   ;

structPatternElements
   : structPatternFields (COMMA structPatternEtCetera?)?
   | structPatternEtCetera
   ;

structPatternFields
   : structPatternField (COMMA structPatternField)*
   ;

structPatternField
   : tupleIndex COLON pattern
   | identifier COLON pattern
   | KW_REF? KW_MUT? identifier
   ;

structPatternEtCetera
   : DOTDOT
   ;

tupleStructPattern
   : pathInExpr LPAREN tupleStructItems? RPAREN
   ;

tupleStructItems
   : pattern (COMMA pattern)* COMMA?
   ;

tuplePattern
   : LPAREN tuplePatternItems? RPAREN
   ;

tuplePatternItems
   : pattern COMMA
   | restPattern
   | pattern (COMMA pattern)+ COMMA?
   ;

groupedPattern
   : LPAREN pattern RPAREN
   ;

slicePattern
   : LSQUAREBRACKET slicePatternItems? RSQUAREBRACKET
   ;

slicePatternItems
   : pattern (COMMA pattern)* COMMA?
   ;

pathPattern
   : pathInExpr
   | qualifiedPathInExpr
   ;

identifier
   : NON_KEYWORD_IDENTIFIER
   | RAW_IDENTIFIER
   ;


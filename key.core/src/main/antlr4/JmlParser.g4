parser grammar JmlParser;

options { tokenVocab=JmlLexer; }

@header {
  import de.uka.ilkd.key.util.parsing.*;
}

@members {
  private SyntaxErrorReporter errorReporter = new SyntaxErrorReporter(getClass());
  public SyntaxErrorReporter getErrorReporter() { return errorReporter;}
}


classlevel_comments: classlevel_comment* EOF;
classlevel_comment: classlevel_element | modifiers | set_statement;
classlevel_element0: modifiers? (classlevel_element modifiers?);
classlevel_element
  : class_invariant /*| depends_clause*/     | method_specification
  | method_declaration  | field_declaration  | represents_clause
  | history_constraint  | initially_clause   | class_axiom
  | monitors_for_clause | readable_if_clause | writable_if_clause
  | datagroup_clause    | set_statement      | nowarn_pragma
  | accessible_clause   | assert_statement   | assume_statement
  ;

methodlevel_comment: (modifiers? methodlevel_element modifiers?)* EOF;
methodlevel_element
  : field_declaration | set_statement | merge_point_statement
  | loop_specification | assert_statement | assume_statement | nowarn_pragma
  | debug_statement | block_specification | block_loop_specification
  | assert_statement | assume_statement
 ;

modifiers: modifier+;
modifier
  : mod = (ABSTRACT | FINAL | GHOST | HELPER | INSTANCE | MODEL | NON_NULL
  | NULLABLE | NULLABLE_BY_DEFAULT | PRIVATE | PROTECTED | PUBLIC | PURE
  | STRICTLY_PURE | SPEC_PROTECTED | SPEC_PUBLIC | STATIC | TWO_STATE
  | NO_STATE | SPEC_JAVA_MATH | SPEC_SAFE_MATH | SPEC_BIGINT_MATH
  | CODE_JAVA_MATH | CODE_SAFE_MATH | CODE_BIGINT_MATH)
 ;



class_axiom: AXIOM expression SEMI_TOPLEVEL;
initially_clause: INITIALLY expression SEMI_TOPLEVEL;
class_invariant: INVARIANT expression SEMI_TOPLEVEL;
//axiom_name: AXIOM_NAME_BEGIN IDENT AXIOM_NAME_END;
method_specification: (also_keyword)* spec_case ((also_keyword)+ spec_case)*;
also_keyword: (ALSO | FOR_EXAMPLE | IMPLIES_THAT);
spec_case:
  (modifiers)?
  behavior=(BEHAVIOR | NORMAL_BEHAVIOR | MODEL_BEHAVIOUR | EXCEPTIONAL_BEHAVIOUR
           | BREAK_BEHAVIOR | CONTINUE_BEHAVIOR | RETURN_BEHAVIOR )?
  spec_body
;

/*spec_var_decls: (old_clause | FORALL expression)+;
spec_header: requires_clause+;*/

spec_body: a+=clause+ (NEST_START inner+=clause* (also_keyword+ spec_body)* NEST_END)?;
clauseEOF: clause EOF;
clause
  :
  ( ensures_clause   | requires_clause     | measured_by_clause
  | captures_clause  | diverges_clause     | working_space_clause
  | duration_clause  | when_clause         | assignable_clause | accessible_clause
  | signals_clause   | signals_only_clause | variant_function  | name_clause
  | breaks_clause    | continues_clause    | returns_clause    | separates_clause
  | determines_clause
  );

// clauses
targetHeap : SPECIAL_IDENT+;
ensures_clause: ENSURES targetHeap? predornot SEMI_TOPLEVEL;
requires_clause: REQUIRES targetHeap? predornot SEMI_TOPLEVEL;
measured_by_clause: MEASURED_BY predornot (COMMA predornot)* SEMI_TOPLEVEL;
captures_clause: CAPTURES predornot SEMI_TOPLEVEL;
diverges_clause: DIVERGES predornot SEMI_TOPLEVEL;
working_space_clause: WORKING_SPACE predornot SEMI_TOPLEVEL;
duration_clause: DURATION predornot SEMI_TOPLEVEL;
when_clause: WHEN predornot SEMI_TOPLEVEL;
accessible_clause
:
  ACCESSIBLE targetHeap?
                    (lhs=expression COLON)? rhs=storeRefUnion
                    (MEASURED_BY mby=expression)?
    SEMI_TOPLEVEL;
assignable_clause: (ASSIGNABLE | MODIFIABLE) targetHeap? (storeRefUnion | STRICTLY_NOTHING) SEMI_TOPLEVEL;
//depends_clause: DEPENDS expression COLON storeRefUnion (MEASURED_BY expression)? ;
//decreases_clause: DECREASES termexpression (COMMA termexpression)*;
represents_clause
  : REPRESENTS lhs=expression
    (((LARROW|EQUAL_SINGLE) (rhs=expression|t=storeRefUnion))
    | (SUCH_THAT predicate))
    SEMI_TOPLEVEL
  ;

separates_clause
  : SEPARATES
    sep=infflowspeclist
    ( DECLASSIFIES   decl+=infflowspeclist
    | ERASES        erase+=infflowspeclist
    | NEW_OBJECTS  newobj+=infflowspeclist
    )*
    SEMI_TOPLEVEL
  ;

loop_separates_clause
  : LOOP_SEPARATES
    sep=infflowspeclist
    (NEW_OBJECTS newobj+=infflowspeclist)*
    SEMI_TOPLEVEL
  ;

infflowspeclist
  : NOTHING
  | expressionlist
  ;

determines_clause
  : DETERMINES
    determined=infflowspeclist
    BY (byItself=ITSELF|by=infflowspeclist)
    ( DECLASSIFIES decl+=infflowspeclist
    | ERASES       erases+=infflowspeclist
    | NEW_OBJECTS newObs+=infflowspeclist
    )*
    SEMI_TOPLEVEL
  ;

loop_determines_clause
  : LOOP_DETERMINES
    det=infflowspeclist
    BY ITSELF
    (NEW_OBJECTS newObs+=infflowspeclist)*
    SEMI_TOPLEVEL
  ;

signals_clause: SIGNALS LPAREN referencetype (IDENT)? RPAREN (predornot)? SEMI_TOPLEVEL;
signals_only_clause: SIGNALS_ONLY (NOTHING |referencetype (COMMA referencetype)*)  SEMI_TOPLEVEL;
breaks_clause: BREAKS LPAREN (lbl=IDENT)? RPAREN (predornot)? SEMI_TOPLEVEL;
continues_clause: CONTINUES LPAREN (lbl=IDENT)? RPAREN (predornot)? SEMI_TOPLEVEL;
returns_clause: RETURNS predornot? SEMI_TOPLEVEL;

name_clause: SPEC_NAME STRING_LITERAL SEMICOLON ;
//old_clause: OLD modifiers type IDENT INITIALISER ;

field_declaration: typespec IDENT (LBRACKET RBRACKET)* initialiser? SEMI_TOPLEVEL;
method_declaration: typespec IDENT param_list (method_body|SEMI_TOPLEVEL);
method_body: LBRACE RETURN expression SEMI_TOPLEVEL RBRACE;
param_list: LPAREN (param_decl (COMMA param_decl)*)? RPAREN;
param_decl: ((NON_NULL | NULLABLE))? typespec p=IDENT (LBRACKET RBRACKET)*;
history_constraint: CONSTRAINT expression;
datagroup_clause: (in_group_clause | maps_into_clause);
monitors_for_clause: MONITORS_FOR expression;
readable_if_clause: READABLE expression;
writable_if_clause: WRITABLE expression;
in_group_clause: IN expression;
maps_into_clause: MAPS expression;
nowarn_pragma: NOWARN expression;
debug_statement: DEBUG expression;
set_statement: SET expression EQUAL_SINGLE expression SEMI_TOPLEVEL;
merge_point_statement:
  MERGE_POINT
  (MERGE_PROC (proc=STRING_LITERAL))?
  (mergeparamsspec)?
  SEMI_TOPLEVEL
;
loop_specification
  : loop_invariant
    ( loop_invariant
    | determines_clause
    | loop_separates_clause
    | loop_determines_clause
    | assignable_clause
    | loop_assignable_clause
    | variant_function)*;

loop_invariant: LOOP_INVARIANT targetHeap? expression SEMI_TOPLEVEL;
loop_assignable_clause: (LOOP_ASSIGNABLE | ASSIGNABLE | MODIFIABLE) targetHeap? (storeRefUnion | STRICTLY_NOTHING) SEMI_TOPLEVEL;
variant_function: DECREASING expression (COMMA expression)* SEMI_TOPLEVEL;
//loop_separates_clause: SEPARATES expression;
//loop_determines_clause: DETERMINES expression;
assume_statement: ASSUME expression SEMI_TOPLEVEL;
initialiser: EQUAL_SINGLE expression;
block_specification: method_specification;
block_loop_specification:
  loop_contract_keyword spec_case ((also_keyword)+ loop_contract_keyword spec_case)*;
loop_contract_keyword: LOOP_CONTRACT;
assert_statement: (ASSERT expression | UNREACHABLE) SEMI_TOPLEVEL;
//breaks_clause: BREAKS expression;
//continues_clause: CONTINUES expression;
//returns_clause: RETURNS expression;


mergeparamsspec:
    MERGE_PARAMS
      LBRACE
          latticetype=IDENT COLON
          LPAREN
              (phType=typespec)
              (phName=IDENT)
          RPAREN

          RARROW

          LBRACE
              (abstrPred+=predicate)
              (COMMA abstrPred+=predicate)*
          RBRACE
      RBRACE
;

termexpression: expression;

storeRefUnion: list = storeRefList;
storeRefList: storeref (COMMA storeref)*;
storeRefIntersect: storeRefList;
storeref: (NOTHING | EVERYTHING | NOT_SPECIFIED |  STRICTLY_NOTHING | storeRefExpr);
createLocset: (LOCSET | SINGLETON) LPAREN exprList RPAREN;
exprList: expression (COMMA expression)*;
storeRefExpr: expression;
predornot: (predicate |NOT_SPECIFIED | SAME);
predicate: expression;

expressionEOF: (expression|storeref)  EOF;
expression: conditionalexpr;
conditionalexpr: equivalenceexpr (QUESTIONMARK conditionalexpr COLON conditionalexpr)?;
equivalenceexpr: impliesexpr (EQV_ANTIV impliesexpr)*;
impliesexpr: a=logicalorexpr (IMPLIES b=impliesforwardexpr | (IMPLIESBACKWARD c+=logicalorexpr)+)?;
impliesforwardexpr: a=logicalorexpr (IMPLIES b=impliesforwardexpr)?;
logicalorexpr: logicalandexpr (LOGICALOR logicalandexpr)*;
logicalandexpr: inclusiveorexpr (LOGICALAND inclusiveorexpr)*;
inclusiveorexpr: exclusiveorexpr (INCLUSIVEOR exclusiveorexpr)*;
exclusiveorexpr: andexpr (XOR andexpr)*;
andexpr: equalityexpr (AND equalityexpr)*;
equalityexpr: relationalexpr (EQ_NEQ relationalexpr)*;

relationalexpr
  : shiftexpr
  | relational_lockset
  | relational_chain
  | instance_of
  | st_expr
  ;

st_expr: shiftexpr ST shiftexpr;
instance_of: shiftexpr INSTANCEOF typespec;
relational_chain:  shiftexpr ( (op+=(GT | GEQ) shiftexpr)
                             | (op+=(LT | LEQ) shiftexpr))+;
relational_lockset: shiftexpr (LOCKSET_LT|LOCKSET_LEQ) postfixexpr;

shiftexpr: additiveexpr (op+=(SHIFTRIGHT|SHIFTLEFT|UNSIGNEDSHIFTRIGHT) additiveexpr)*;
additiveexpr: multexpr (op+=(PLUS|MINUS) multexpr)*;
multexpr: unaryexpr (op+=(MULT|DIV|MOD) unaryexpr)*;
unaryexpr: (PLUS unaryexpr | MINUS DECLITERAL | MINUS unaryexpr | castexpr | unaryexprnotplusminus);
castexpr: LPAREN typespec RPAREN unaryexpr;
unaryexprnotplusminus: (NOT unaryexpr | BITWISENOT unaryexpr | postfixexpr);
postfixexpr: primaryexpr (primarysuffix)*;
primaryexpr
  : constant
  | ident
  | inv
  | inv_free
  | true_
  | false_
  | null_
  | jmlprimary
  | new_expr
  | array_initializer
  ;
this_: THIS;
ident: IDENT | JML_IDENT | SPECIAL_IDENT | THIS | SUPER;
inv:INV;
inv_free:INV_FREE;
true_:TRUE;
false_:FALSE;
null_:NULL;
transactionUpdated: TRANSACTIONUPDATED LPAREN expression RPAREN;

primarysuffix
  : DOT (IDENT | TRANSIENT | THIS | INV | INV_FREE | MULT)
    (LPAREN (expressionlist)? RPAREN)? #primarySuffixAccess
  | (LPAREN (expressionlist)? RPAREN)  #primarySuffixCall
  | LBRACKET (from=expression (DOTDOT to=expression)? | MULT) RBRACKET #primarySuffixArray
  ;

new_expr: NEW type (LPAREN (expressionlist)? RPAREN | array_dimensions (array_initializer)?);
array_dimensions: array_dimension;
array_dimension: LBRACKET (expression)? RBRACKET;
array_initializer: LBRACE expressionlist RBRACE;
expressionlist: expression (COMMA expression)*;
constant: javaliteral;
javaliteral
  : integerliteral
  | fractionalliteral
  | stringliteral
  | charliteral
  ;
stringliteral: STRING_LITERAL;
charliteral: CHAR_LITERAL;
integerliteral: (HEXLITERAL | DECLITERAL | OCTLITERAL | BINLITERAL);
fractionalliteral: FLOAT_LITERAL | DOUBLE_LITERAL | REAL_LITERAL;
jmlprimary
  : RESULT                                                                            #primaryResult
  | EXCEPTION                                                                         #primaryException
  | infinite_union_expr                                                               #pignore1
  | specquantifiedexpression                                                          #pignore2
  | bsumterm                                                                          #pignore3
  | seqdefterm                                                                        #pignore4
  | oldexpression                                                                     #pignore5
  | bigint_math_expression                                                            #primaryBigintMathExpression
  | safe_math_expression                                                              #primarySafeMathExpression
  | java_math_expression                                                              #primaryJavaMathExpression
  | beforeexpression                                                                  #pignore6
  | transactionUpdated                                                                #pignore7
  | BACKUP LPAREN expression RPAREN                                                   #primaryBackup
  | PERMISSION LPAREN expression RPAREN                                               #primaryPermission
  | NONNULLELEMENTS LPAREN expression RPAREN                                          #primaryNNE
  | INFORMAL_DESCRIPTION                                                              #primaryInformalDesc
  //| JML_IDENT (LPAREN (expressionlist)? RPAREN)                                       #primaryDLCall
  | MAPEMPTY                                                                          #primaryMapEmpty
  | mapExpression LPAREN (expressionlist)? RPAREN                                     #primaryMapExpr
  | fpOperator LPAREN expression RPAREN                                               #primaryFloatingPoint
  | SEQ2MAP LPAREN (expressionlist)? RPAREN                                           #primarySeq2Map
  | NOT_MODIFIED LPAREN storeRefUnion RPAREN                                          #primaryNotMod
  | NOT_ASSIGNED LPAREN storeRefUnion RPAREN                                          #primaryNotAssigned
  | FRESH LPAREN expressionlist RPAREN                                                #primaryFresh
  | REACH LPAREN storeref COMMA expression COMMA expression (COMMA expression)? RPAREN #primaryReach
  | REACHLOCS LPAREN storeref COMMA expression (COMMA expression)? RPAREN             #primaryReachLocs
  | DURATION LPAREN expression RPAREN                                                 #primaryDuration
  | SPACE LPAREN expression RPAREN                                                    #primarySpace
  | WORKINGSPACE LPAREN expression RPAREN                                             #primaryWorksingSpace
  | LPAREN expression RPAREN                                                          #primaryParen
  | TYPEOF LPAREN expression RPAREN                                                   #primaryTypeOf
  | ELEMTYPE LPAREN expression RPAREN                                                 #primaryElemtype
  | TYPE_SMALL LPAREN typespec RPAREN                                                 #primayTypeSpec
  | LOCKSET                                                                           #primaryLockset
  | IS_INITIALIZED LPAREN referencetype RPAREN                                        #primaryIsInitialised
  | INVARIANT_FOR LPAREN expression RPAREN                                            #primaryInvFor
  | INVARIANT_FREE_FOR LPAREN expression RPAREN                                       #primaryInvFreeFor
  | STATIC_INVARIANT_FOR LPAREN referencetype RPAREN                                  #primaryStaticInv
  | STATIC_INVARIANT_FREE_FOR LPAREN referencetype RPAREN                             #primaryStaticInvFree
  | LPAREN LBLNEG IDENT expression RPAREN                                             #primaryLblNeg
  | LPAREN LBLPOS IDENT expression RPAREN                                             #primaryLblPos
  | INDEX                                                                             #primaryIndex
  | VALUES                                                                            #primaryValues
  | STRING_EQUAL LPAREN expression COMMA expression RPAREN                            #primaryStringEq
  | EMPTYSET                                                                          #primaryEmptySet
  | STOREREF LPAREN storeRefUnion RPAREN                                              #primaryStoreRef
  | LOCSET LPAREN fieldarrayaccess (COMMA fieldarrayaccess)* RPAREN                   #primaryCreateLocset
  | SINGLETON LPAREN expression RPAREN                                                #primaryCreateLocsetSingleton
  | UNION LPAREN storeRefUnion RPAREN                                                 #primaryUnion
  | INTERSECT LPAREN storeRefIntersect RPAREN                                         #primaryIntersect
  | SETMINUS LPAREN storeref COMMA storeref RPAREN                                    #primarySetMinux
  | ALLFIELDS LPAREN expression RPAREN                                                #primaryAllFields
  | ALLOBJECTS LPAREN storeref RPAREN                                                 #primaryAllObj
  | UNIONINF LPAREN (boundvarmodifiers)? quantifiedvardecls SEMI (predicate SEMI | SEMI)? storeref RPAREN
                                                                                     #primaryUnionInf
  | DISJOINT LPAREN storeRefList RPAREN                                              #primaryDisjoint
  | SUBSET LPAREN storeref COMMA storeref RPAREN                                     #primarySubset
  | NEWELEMSFRESH LPAREN storeref RPAREN                                             #primaryNewElemsfrehs
  | sequence                                                                         #primaryignore10
  ;

fieldarrayaccess: (ident|this_|super_) (fieldarrayaccess_suffix)*;
fieldarrayaccess_suffix
    : DOT (ident | inv | inv_free | this_ | super_ | TRANSIENT | INV | INV_FREE)
    | LBRACKET (expression) RBRACKET
;

super_: SUPER;

sequence
  : SEQEMPTY                                                              #sequenceEmpty
  | seqdefterm                                                            #sequenceIgnore1
  | (SEQSINGLETON | SEQ) LPAREN exprList RPAREN                           #sequenceCreate
  | SEQSUB LPAREN expression COMMA expression COMMA expression RPAREN     #sequenceSub
  | SEQREVERSE LPAREN expression RPAREN                                   #sequenceReverse
  | SEQREPLACE LPAREN expression COMMA expression COMMA expression RPAREN #sequenceReplace
  | op=(SEQCONCAT |SEQGET |INDEXOF) LPAREN expression COMMA expression RPAREN #sequenceFuncs
  ;

mapExpression: MAP_GET | MAP_OVERRIDE | MAP_UPDATE | MAP_REMOVE | IN_DOMAIN | DOMAIN_IMPLIES_CREATED | MAP_SIZE | MAP_SINGLETON | IS_FINITE;
fpOperator: FP_ABS | FP_INFINITE | FP_NAN | FP_NEGATIVE | FP_NICE | FP_NORMAL | FP_POSITIVE | FP_SUBNORMAL;
quantifier: FORALL | EXISTS | MIN | MAX | NUM_OF | PRODUCT | SUM;
infinite_union_expr: LPAREN UNIONINF (boundvarmodifiers)? quantifiedvardecls SEMI (predicate SEMI)* storeref RPAREN;
specquantifiedexpression: LPAREN quantifier (boundvarmodifiers)? quantifiedvardecls SEMI (expression SEMI)? expression RPAREN;
oldexpression: (PRE LPAREN expression RPAREN | OLD LPAREN expression (COMMA IDENT)? RPAREN);
java_math_expression: (JAVA_MATH LPAREN expression RPAREN);
safe_math_expression: (SAFE_MATH LPAREN expression RPAREN);
bigint_math_expression: (BIGINT_MATH LPAREN expression RPAREN);
beforeexpression: (BEFORE LPAREN expression RPAREN);
bsumterm: LPAREN BSUM quantifiedvardecls SEMI (expression SEMI expression SEMI expression) RPAREN;
seqdefterm: LPAREN SEQDEF quantifiedvardecls SEMI (expression SEMI expression SEMI expression) RPAREN;
quantifiedvardecls: typespec quantifiedvariabledeclarator (COMMA quantifiedvariabledeclarator)*;
boundvarmodifiers: (NON_NULL | NULLABLE);
typespec: type (dims)?;
dims: (LBRACKET RBRACKET)+;
type: builtintype | referencetype | TYPE;
referencetype: name;
builtintype: BYTE | SHORT | INT | LONG | BOOLEAN | VOID | BIGINT | REAL | LOCSET | SEQ | FREE;
name: ident (DOT ident)*;
quantifiedvariabledeclarator: IDENT dims?;


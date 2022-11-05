grammar Config;

/*
[SMT_SOLVER]
Z3 = {
  name = z3,
  path = "$HOME/bin/z3",
  flags = [ "-T", 25, "-smt2" ]
}
*/

file: (section? kv)*;
section: LBRACKET SYMBOL RBRACKET;
kv: (SYMBOL|STRING) EQUAL value;
value:
    SYMBOL #symbol
  | STRING #string
  | NUMBER #num
  | FLOATING #fp
  | BOOLEAN #bool
  | LBRACE
     (kv (COMMA kv)*)?
    RBRACE #table
  | LBRACKET (value (COMMA value)*)? RBRACKET #list;


COMMENT: '#' ~('\n'|'\r')* -> channel(HIDDEN);
ML_COMMENT: '/*' (ML_COMMENT|.)*?  '*/'->channel(HIDDEN);
WS: ('\n'|'\r'|' '|'\f'|'\t')+ -> channel(HIDDEN);
COMMA:',';
BOOLEAN: 'true'|'false'|'FALSE'|'TRUE';
FLOATING: [+-]? [0-9]* '.' [0-9]+;
NUMBER: [+-]? [0-9]+;
STRING: '"' ~( '"' )* '"';
RBRACE:'}';
LBRACE:'{';
LBRACKET: '[';
RBRACKET: ']';
EQUAL: '=';
SYMBOL: [_a-zA-Z] [a-zA-Z_]*;

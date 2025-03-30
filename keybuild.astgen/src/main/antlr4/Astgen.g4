grammar Astgen;

@option{}

@header{}

/**

package xxx;

class Expr
  (extends ... )
  (implements ... )
{
    TypeName[*?] name;
}
*/


file: packageClause command*;
command: packageClause | astNode;
packageClause: 'package' ident ';';
astNode: ((ABSTRACT|FINAL)? CLASS | INTERFACE) ident
         extendsClause?
         implementsClause?
        '{'  field*  '}'
        ;
extendsClause: 'extends' ident;
implementsClause: 'implements' i+=ident (',' i+=ident)*;
field: javadoc? type=ident (isnullable='?')? (islist='*')? name=ident;
javadoc: JAVADOC;

ident: IDENT;

JAVADOC: '/**' .*? '*/';
FINAL:'final';
ABSTRACT: 'abstract';
CLASS: 'class';
INTERFACE: 'interface';
IDENT: [a-zA-Z] [a-zA-Z0-9]*;





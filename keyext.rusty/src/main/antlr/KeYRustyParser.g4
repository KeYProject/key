parser grammar KeYRustyParser;

import KeYParser;

options { tokenVocab = KeYRustyLexer; }

@header {
package org.key_project.rusty.parser;
}

varexpId
 : APPLY_UPDATE_ON_RIGID
 | DROP_EFFECTLESS_ELEMENTARIES
 | SIMPLIFY_IF_THEN_ELSE_UPDATE
 | EQUAL_UNIQUE
 | NEW_TYPE_OF
 | NEW_DEPENDING_ON
 | NEW
 | NEW_LOCAL_VARS
 | STORE_TERM_IN
 | STORE_EXPR_IN
 | HAS_INVARIANT
 | GET_INVARIANT
 | GET_VARIANT
 ;

elementary_update_term: a=mutating_update_term (ASSIGN b=mutating_update_term)?;
mutating_update_term: a=equivalence_term (MUTATE b=equivalence_term)?;

primitive_term:
    termParen
  | ifThenElseTerm
  | ifExThenElseTerm
  | abbreviation
  | accessterm
  | mRef_term
  | literals
  ;

mRef_term : REF_M LESS simple_ident GREATER;

typemapping
    : (AND MUT?)? simple_ident;
lexer grammar JavaKeYLexer;

@header {
}

@annotateclass{ @SuppressWarnings("all") }

import KeYLexer;

// Keywords used in schema variable declarations
TERMLABEL : '\\termlabel';

// used in contracts
MODIFIABLE : '\\modifiable';

// Keywords used in program variable declarations
PROGRAMVARIABLES : '\\programVariables';

// Keywords for varcond and related stuff
STORE_TERM_IN : '\\storeTermIn';
STORE_STMT_IN : '\\storeStmtIn';
HAS_INVARIANT : '\\hasInvariant';
GET_INVARIANT : '\\getInvariant';
GET_FREE_INVARIANT: '\\getFreeInvariant';
GET_VARIANT: '\\getVariant';
IS_LABELED: '\\isLabeled';

SAME_OBSERVER : '\\sameObserver';
DEPENDINGON : '\\dependingOn';
DISJOINTMODULONULL  : '\\disjointModuloNull';
DROP_EFFECTLESS_STORES : '\\dropEffectlessStores';
ENUM_CONST : '\\enumConstant';
FREELABELIN : '\\freeLabelIn';
FIELDTYPE : '\\fieldType';
FINAL : '\\final';
ELEMSORT : '\\elemSort';
HASLABEL : '\\hasLabel';
HASSUBFORMULAS : '\\hasSubFormulas';
ISARRAY:'\\isArray';
ISARRAYLENGTH:'\\isArrayLength';
ISCONSTANT: '\\isConstant';
ISENUMTYPE:'\\isEnumType';
ISINDUCTVAR:'\\isInductVar';
ISLOCALVARIABLE : '\\isLocalVariable';
ISOBSERVER : '\\isObserver';
METADISJOINT : '\\metaDisjoint';
ISTHISREFERENCE:'\\isThisReference';
DIFFERENTFIELDS:'\\differentFields';
ISREFERENCE:'\\isReference';
ISREFERENCEARRAY:'\\isReferenceArray';
ISSTATICFIELD : '\\isStaticField';
ISMODELFIELD : '\\isModelField';
ISINSTRICTFP : '\\isInStrictFp';
NEW_DEPENDING_ON: '\\newDependingOn';
NEW_LOCAL_VARS: '\\newLocalVars';
NEWLABEL : '\\newLabel';
CONTAINS_ASSIGNMENT : '\\containsAssignment';
// label occurs again for character `!'
NOTFREEIN : '\\notFreeIn';
STATIC : '\\static';
STATICMETHODREFERENCE : '\\staticMethodReference';
MAXEXPANDMETHOD : '\\mayExpandMethod';

// inclusion and stuff, things that (usually) come at the beginning
// of the file
CLASSPATH:'\\classpath';
BOOTCLASSPATH:'\\bootclasspath';
NODEFAULTCLASSES:'\\noDefaultClasses';
JAVASOURCE:'\\javaSource'; // TODO: remove

CHOOSECONTRACT : '\\chooseContract';
CONTRACTS : '\\contracts';
INVARIANTS : '\\invariants';

// The first three guys are not really meta operators, treated separately
IN_TYPE : '\\inType';
IS_ABSTRACT_OR_INTERFACE : '\\isAbstractOrInterface';
IS_FINAL : '\\isFinal';
CONTAINERTYPE : '\\containerType';

// types that need to be declared as keywords
//LOCSET : '\\locset';
//SEQ : '\\seq';
//BIGINT : '\\bigint';

/**
  * Here we have to accept all strings of ki01           ERROR_CHAR 0:\                                                 nd \\[a-z_]
  * and make the decision our selves as to what to do with it
  * (i.e. is it a modality, keyword, or possibly something else)
  */
MODALITYBB:	'\\[[' -> more, pushMode(modBoxBox);

MODAILITYGENERIC3: '\\diamond_transaction'    -> more, pushMode(modGeneric);
MODAILITYGENERIC5: '\\box_transaction'        -> more, pushMode(modGeneric);
MODAILITYGENERIC6: '\\throughout'             -> more, pushMode(modGeneric);
MODAILITYGENERIC7: '\\throughout_transaction' -> more, pushMode(modGeneric);

/* weigl: not working
MODAILITYGENERIC:
      ('\\modality' | '\\diamond' | '\\diamond_transaction'
      '\\box' | '\\box_transaction' | '\\throughout' | '\\throughout_transaction')
      -> more, pushMode(modGeneric);
*/
//BACKSLASH:  '\\';

DOC_COMMENT
   : '/*!' -> more , pushMode (docComment)
   ;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

import java.util.List;

@Root
abstract class BaseAstNode implements AstNode {
    @Nullable Position position;
}

/**
 * Represents an abbreviation definition.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * abbreviation: ABBREVIATION ident EQUALS term NEWLINE;
 * }</pre>
 */
class Abbreviation {
    String name;
    Term definition;
}


/**
 * Represents an abstract sort declaration.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * ABSTRACT? (sortIds=simple_ident_dots_comma_list | parametric_sort_decl) (EXTENDS sortExt=extends_sorts)? SEMI;
 * }</pre>
 */
class AbstractSortDecl {
    boolean isAbstract;
    List<SimpleIdentDots> sortIds;
    @Nullable String docComment;
    @Nullable FormalSortParamDecls formalSortParamDecls;
    @Nullable ExtendsSorts extendsSorts;
}


/**
 * Represents an access term (for information flow control).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * access_term: ACCESS location_term;
 * }</pre>
 */
class AccessTerm {
    LocationTerm location;
}


/**
 * Represents an activated choice (category:choice).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * activated_choice: cat=IDENT COLON choice_=IDENT;
 * }</pre>
 */
class ActivatedChoice {
    String category;
    String choice;
}


/**
 * Represents add clause in taclet.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * add: term;
 * }</pre>
 */

class Add {
    Term term;
}


/**
 * Represents add program variables clause in taclet.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * add_prog_vars: ident COLON keyjavatype;
 * }</pre>
 */

class AddProgVars {
    String name;
    KeyJavaType type;
}


/**
 * Represents add rules clause in taclet.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * add_rules: simple_ident_comma_list;
 * }</pre>
 */

class AddRules {
    List<String> ruleNames;
}


/**
 * Represents an alias sort declaration.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * ALIAS simple_ident_dots EQUALS sortId SEMI;
 * }</pre>
 */

class AliasDeclimplements {
    @Nullable String docComment;
    SimpleIdentDots aliasName;
    SortId targetSort;


}


/**
 * Represents argument sorts.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * arg_sorts: (LPAREN sortId (COMMA sortId)* RPAREN)?;
 * }</pre>
 */

class ArgSorts {
    List<SortId> sorts;

}

/**
 * Represents argument sorts or formula (for transformers).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * arg_sorts_or_formula: (LPAREN arg_sorts_or_formula_helper (COMMA arg_sorts_or_formula_helper)* RPAREN)?;
 * arg_sorts_or_formula_helper: sortId | FORMULA;
 * }</pre>
 */
class ArgSortsOrFormula {
    List<Object> items; // List of SortId or Boolean (true = FORMULA keyword)

}

/**
 * Represents an attribute access (object.field).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * attribute: DOT ident;
 * }</pre>
 */

class Attribute {
    String fieldName;
}


/**
 * Base abstract class for all AST nodes providing common position tracking.
 *
 * @author Cline
 * @version 1.0
 */


/**
 * Represents a boolean literal (true/false).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * boolean_literal: TRUE | FALSE;
 * }</pre>
 */

class BooleanLiteral extends Literals {
    boolean value;
}


/**
 * Represents bound variables in quantifiers.
 * Corresponds to: var=one_bound_variable (COMMA var=one_bound_variable)* SEMI;
 *
 * @author Cline
 * @version 1.0
 */

class BoundVariables {
    List<OneBoundVariable> variables;


}


/**
 * Represents a brace suffix (anonymous object creation).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * brace_suffix: LBRACE (term (COMMA term)*)? RBRACE;
 * }</pre>
 */

class BraceSuffix {
    java.util.List<Term> elements;

}


/**
 * Represents a bracket suffix heap (heap access after bracket).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * bracket_suffix_heap: (LBRACKET term RBRACKET)*;
 * }</pre>
 */

class BracketSuffixHeap {
    java.util.List<Term> indices;

}


/**
 * Represents a bracket term (parenthesized expression).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * bracket_term: LPAREN term RPAREN bracket_suffix_heap?;
 * }</pre>
 */

class BracketTerm {
    Term inner;
    @Nullable BracketSuffixHeap suffix;


}


/**
 * Represents a method/function call.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * call: LPAREN (term (COMMA term)*)? RPAREN;
 * }</pre>
 */

class Call {
    java.util.List<Term> arguments;

}


/**
 * Represents a cast term ((type)term).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * cast_term: LPAREN sortid RPAREN term;
 * }</pre>
 */

class CastTerm {
    SortId targetType;
    Term operand;


}


/**
 * Represents a char literal.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * char_literal: CHAR_LITERAL;
 * }</pre>
 */

class CharLiteral extends Literals {
    String value;


}


/**
 * Represents a choice with optional options.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * choice: maindoc+=DOC_COMMENT* category=IDENT (COLON LBRACE optionDecl (COMMA optionDecl)* RBRACE)?;
 * }</pre>
 */

class Choice {
    List<String> docComments;
    String category;
    @Nullable List<String> optionDecls;


}


/**
 * Represents a configuration key (simple identifier with dots).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * ckey: simple_ident_dots;
 * }</pre>
 */

class CKey {
    String key;
}


/**
 * Represents a configuration key-value pair.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * ckv: ckey EQUALS cvalue NEWLINE;
 * }</pre>
 */

class CKV {
    CKey key;
    CValue value;
}


/**
 * Represents a comparison term (left <,>,=<,>= right).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * comparison_term: left=term (LT | GT | LE | GE) right=term;
 * }</pre>
 */

class ComparisonTerm {
    enum Op {LT, GT, LE, GE}

    Term left;
    Term right;
    Op operator;


}


/**
 * Represents a configuration file.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * cfile: (ckv)* EOF;
 * }</pre>
 */

class ConfigurationFile {
    List<CKV> entries;

}


/**
 * Represents a conjunction term (left && right).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * conjunction_term: left=term AND right=term;
 * }</pre>
 */

class ConjunctionTerm {
    Term left;
    Term right;


}


/**
 * Represents contracts container.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * contracts: CONTRACTS LBRACE (rules_or_axioms SEMI)* RBRACE;
 * }</pre>
 */

class Contracts {
    List<RulesOrAxioms> items;

}


/**
 * Represents a configuration value (string).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * cvalue: STRING;
 * }</pre>
 */

class CValue {
    String value;
}


/**
 * Represents a datatype constructor.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * datatype_constructor: name=simple_ident arg_sorts;
 * }</pre>
 */

class DatatypeConstructor {
    SimpleIdentDots name;
    ArgSorts argSorts;
}


/**
 * Represents a datatype declaration.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * datatype_decl: doc=DOC_COMMENT? (FREE)? name=simple_ident formal_sort_param_decls? EQUALS datatype_constructor (OR datatype_constructor)* SEMI;
 * }</pre>
 */

class DatatypeDecl {
    @Nullable String docComment;
    boolean isFree;
    SimpleIdentDots name;
    @Nullable FormalSortParamDecls formalSortParams;
    List<DatatypeConstructor> constructors;
}


/**
 * Represents datatype declarations.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * datatype_decls: DATATYPES LBRACE datatype_decl* RBRACE;
 * }</pre>
 */

class DatatypeDecls {
    List<DatatypeDecl> decls;

}

/**
 * Base interface for all declaration types in KeY specification files.
 *
 * @author Cline
 * @version 1.0
 */

interface Declaration {
    // Marker interface for all declarations
}


/**
 * Represents a disjunction term (left || right).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * disjunction_term: left=term OR right=term;
 * }</pre>
 */

class DisjunctionTerm {
    Term left;
    Term right;


}


/**
 * Represents an elementary update term (location := value).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * elementary_update_term: location_term ASSIGN term;
 * }</pre>
 */

class ElementaryUpdateTerm {
    LocationTerm location;
    Term value;


}


/**
 * Represents an equality term (left == right or left != right).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * equality_term: left=term (EQUALS | NOT_EQUALS) right=term;
 * }</pre>
 */

class EqualityTerm {
    Term left;
    Term right;
    boolean isEquality;


}


/**
 * Represents an equivalence term (left <-> right).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * equivalence_term: left=term EQUIV right=term;
 * }</pre>
 */

class EquivalenceTerm {
    Term left;
    Term right;


}


/**
 * Represents extends sort clause.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * extends_sorts: sortId (COMMA sortId)*;
 * }</pre>
 */

class ExtendsSorts {
    List<SortId> sortIds;

}

/**
 * Represents the root of a KeY specification file.
 * Corresponds to the grammar rule: file: DOC_COMMENT* (profile? preferences? decls problem? proof?) EOF;
 *
 * @author Cline
 * @version 1.0
 */

class File {
    List<String> docComments;
    @Nullable Profile profile;
    @Nullable Preferences preferences;
    List<Declaration> decls;
    @Nullable Problem problem;
    @Nullable Proof proof;
}


/**
 * Represents a float literal.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * float_literal: FLOAT_LITERAL;
 * }</pre>
 */

class FloatLiteral extends Literals {
    String value;
}


/**
 * Represents formal sort arguments (type parameters).
 * Corresponds to: OPENTYPEPARAMS sortId (COMMA sortId)* CLOSETYPEPARAMS;
 *
 * @author Cline
 * @version 1.0
 */

class FormalSortArgs {
    List<SortId> sortIds;


}


/**
 * Represents formal sort parameter declarations.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * formal_sort_param_decls: LBRACKET sortId (COMMA sortId)* RBRACKET;
 * }</pre>
 */

class FormalSortParamDecls {
    List<SortId> sortIds;

}

/**
 * Represents a formula (wraps a Term).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * formula: t=term;
 * }</pre>
 */

class Formula {
    Term term;
}


/**
 * Represents a function declaration.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * func_decl: doc=DOC_COMMENT? (UNIQUE)? retSort = sortId func_name = funcpred_name formal_sort_param_decls? whereToBind=where_to_bind? argSorts = arg_sorts SEMI;
 * }</pre>
 */

class FuncDecl {
    @Nullable String docComment;
    boolean isUnique;
    SortId returnSort;
    FuncPredName name;
    @Nullable FormalSortParamDecls formalSortParams;
    @Nullable WhereToBind whereToBind;
    ArgSorts argSorts;
}


/**
 * Represents function declarations.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * func_decls: FUNCTIONS LBRACE (func_decl)* RBRACE;
 * }</pre>
 */

class FuncDecls {
    List<FuncDecl> decls;

}


/**
 * Represents a function/predicate name with optional sort prefix.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * funcpred_name: (sortId DOUBLECOLON)? (name=simple_ident_dots|num=INT_LITERAL);
 * }</pre>
 */

class FuncPredName {
    @Nullable SortId sortPrefix;
    @Nullable SimpleIdentDots name;
    @Nullable String intLiteral;
}


/**
 * Represents a generic sort declaration.
 * Corresponds to the grammar rule for GENERIC kind in one_sort_decl.
 */

class GenericSortDecl {
    @Nullable String docComment;
    List<String> sortNames;
    @Nullable ExtendsSorts extendsSorts;
    @Nullable FormalSortParamDecls formalParams;


}


/**
 * Represents a goal specification (find clause in taclet).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * goal_spec: term_or_seq;
 * }</pre>
 */

class GoalSpec {
    TermOrSeq termOrSeq;
}


/**
 * Represents a list of goal specifications.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * goal_specs: goal_spec (COMMA goal_spec)*;
 * }</pre>
 */

class GoalSpecs {
    List<GoalSpec> specs;

}


/**
 * Represents an if-ex-then-else term (conditional expression with ? :).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * if_ex_then_else_term: condition QUESTION thenBranch COLON elseBranch;
 * }</pre>
 */

class IfExThenElseTerm {
    Term condition;
    Term thenBranch;
    Term elseBranch;


}


/**
 * Represents an if-then-else term (conditional formula).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * if_then_else_term: IF condition THEN thenBranch ELSE elseBranch END;
 * }</pre>
 */

class IfThenElseTerm {
    Term condition;
    Term thenBranch;
    Term elseBranch;


}


/**
 * Represents an implication term (left ==> right).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * implication_term: left=term IMPLIES right=term;
 * }</pre>
 */

class ImplicationTerm {
    Term left;
    Term right;


}


/**
 * Represents an include statement in a KeY specification file.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * one_include_statement: (INCLUDE | INCLUDELDTS) one_include (COMMA one_include)* SEMI;
 * }</pre>
 */

class IncludeStatement {
    boolean isLdt;
    List<OneInclude> includes;

}


/**
 * Represents an integer literal.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * integer_literal: INT_LITERAL;
 * }</pre>
 */

class IntegerLiteral extends Literals {
    String value;


}


/**
 * Represents invariants container.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * invariants: INVARIANTS LBRACE (rules_or_axioms SEMI)* RBRACE;
 * }</pre>
 */

class Invariants {
    List<RulesOrAxioms> items;

}


/**
 * Represents a KeY Java type.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * key_java_type: ident_dots;
 * }</pre>
 */

class KeyJavaType {
    String typeName;


}


/**
 * Represents a label (for program statements).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * label: LABEL ident COLON;
 * }</pre>
 */

class Label {
    String name;


}


/**
 * Base class for literal values.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * literals: boolean_literal | integer_literal | float_literal | string_literal | char_literal;
 * }</pre>
 */

abstract class Literals {
}


/**
 * Represents a location term (variable or field access).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * location_term: ident (DOT ident)* (LBRACKET term RBRACKET)*?;
 * }</pre>
 */

class LocationTerm {
    String baseName;
    @Nullable Term qualifier;
    java.util.List<String> fieldChain;
    java.util.List<Term> arrayIndices;
}


/**
 * Represents a location set term (for heap operations).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * locset_term: LBRACE (term (COMMA term)*)? RBRACE;
 * }</pre>
 */

class LocsetTerm {
    List<Term> locations;
}


/**
 * Represents a modality term (box/diamond).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * modality_term: (BOX | DIAMOND) program DOT term;
 * }</pre>
 */

class ModalityTerm {
    boolean isBox;
    Term program;
    Term body;


}


/**
 * Represents modifiers for taclets.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * modifiers: LBRACKET ident+=simple_ident (COMMA ident+=simple_ident)* RBRACKET;
 * }</pre>
 */

class Modifiers {
    List<String> modifierNames;
}


/**
 * Represents a negation term (!term).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * negation_term: NOT term;
 * }</pre>
 */

class NegationTerm {
    Term operand;


}


/**
 * Represents a single bound variable.
 * Corresponds to: s=sortId? id=simple_ident;
 *
 * @author Cline
 * @version 1.0
 */

class OneBoundVariable {
    @Nullable SortId sort;
    String name;
}


/**
 * Represents a single contract definition.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * one_contract: ident COLON term NEWLINE modifiable_clause?;
 * }</pre>
 */

class OneContract {
    String name;
    Term formula;
    Term modifiableClause;


}


/**
 * Represents a single include (absolute or relative file).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * one_include: absfile=IDENT | relfile=string_value;
 * }</pre>
 */

class OneInclude {
    String value;
    boolean isAbsolute;


}


/**
 * Represents a single invariant definition.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * one_invariant: ident COLON term (DISPLAY_STRING string)? NEWLINE;
 * }</pre>
 */

class OneInvariant {
    String name;
    Term formula;
    @Nullable String displayName;
}


/**
 * Represents one-of sort clause.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * one_of_sorts: LBRACE sortId (COMMA sortId)* RBRACE;
 * }</pre>
 */

class OneOfSorts {
    List<SortId> sortIds;

}

/**
 * Represents a single schema variable declaration.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * one_schema_var_decl: MODALOPERATOR ... | PROGRAM ... | FORMULA ... | TERMLABEL ... | UPDATE ... | SKOLEMFORMULA ... | (TERM | VARIABLES | VARIABLE | SKOLEMTERM) ...;
 * }</pre>
 */
class OneSchemaVarDecl {
    enum Kind {
        MODAL_OPERATOR, PROGRAM, FORMULA, TERMLABEL, UPDATE, SKOLEM_FORMULA, TERM, VARIABLES, VARIABLE, SKOLEM_TERM
    }

    Kind kind;
    @Nullable SchemaModifiers modifiers;
    @Nullable SortId sortId;
    @Nullable String nameString;
    @Nullable SimpleIdentDots parameter;
    List<String> identifiers;
    @Nullable String modalOpName;
    @Nullable SortId modalOpSort;
}

/**
 * Base interface for single sort declarations.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * one_sort_decl: doc=DOC_COMMENT? (GENERIC ... | PROXY ... | ABSTRACT? ... | ALIAS ...);
 * }</pre>
 */
interface OneSortDecl {
    @Nullable String getDocComment();
}

/**
 * Represents option declarations.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * option_decls: OPTIONSDECL LBRACE (choice SEMI)* RBRACE;
 * }</pre>
 */

class OptionDecls {
    List<Choice> choices;

}

/**
 * Represents a list of options for taclets.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * option_list: LPAREN option_expr (COMMA option_expr)* RPAREN;
 * }</pre>
 */

class OptionList {
    List<OptionExpr> options;
}

/**
 * Represents an options choice declaration.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * options_choice: WITHOPTIONS activated_choice (COMMA activated_choice)* SEMI;
 * }</pre>
 */
class OptionsChoice {
    List<ActivatedChoice> choices;
}


/**
 * Represents a parallel term (multiple updates in parallel).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * parallel_term: (elementary_update_term (COMMA elementary_update_term)*)?;
 * }</pre>
 */

class ParallelTerm {
    List<ElementaryUpdateTerm> updates;

}


/**
 * Represents a predicate declaration.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * pred_decl: doc=DOC_COMMENT? pred_name = funcpred_name formal_sort_param_decls? (whereToBind=where_to_bind)? argSorts=arg_sorts SEMI;
 * }</pre>
 */
class PredDecl {
    @Nullable String docComment;
    FuncPredName name;
    @Nullable FormalSortParamDecls formalSortParams;
    @Nullable WhereToBind whereToBind;
    ArgSorts argSorts;
}

/**
 * Represents predicate declarations.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * pred_decls: PREDICATES LBRACE (pred_decl)* RBRACE;
 * }</pre>
 */
class PredDecls {
    List<PredDecl> decls;

}


/**
 * Represents a preferences/settings declaration in a KeY specification file.
 * Corresponds to: KEYSETTINGS (LBRACE s=string_value? RBRACE | c=cvalue);
 *
 * @author Cline
 * @version 1.0
 */
class Preferences {
    @Nullable String stringValue;
    @Nullable CValue cvalue;
}

/**
 * Represents a problem declaration in a KeY specification file.
 * Corresponds to the grammar rule: problem
 *
 * @author Cline
 * @version 1.0
 */
class Problem {
    @Nullable Term termOrSeq;
    @Nullable String chooseContract;
    @Nullable String proofObligation;
    @Nullable ProofScriptEntry proofScriptEntry;
}


/**
 * Represents a profile declaration in a KeY specification file.
 * Corresponds to: PROFILE name=string_value SEMI;
 *
 * @author Cline
 * @version 1.0
 */

class Profile {
    String name;
}


/**
 * Represents program variable declarations.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * prog_var_decls: PROGRAMVARIABLES LBRACE (keyjavatype var_names SEMI)* RBRACE;
 * }</pre>
 */

class ProgVarDecls {
    List<KeyJavaType> types;
    List<List<String>> varNames;

}

/**
 * Represents a proof declaration in a KeY specification file.
 * Corresponds to: PROOF EOF;
 *
 * @author Cline
 * @version 1.0
 */

class Proof {
}


/**
 * Represents a proof script command.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * proof_script_command: simple_ident_dots LPAREN (STRING (COMMA STRING)*)? RPAREN NEWLINE;
 * }</pre>
 */

class ProofScriptCommand {
    String name;
    java.util.List<String> arguments;
}


/**
 * Represents a proof script entry (either a reference to an external script or an inline script).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * proof_script_entry: string | LBRACE proof_script RBRACE;
 * }</pre>
 */

class ProofScriptEntry {
    @Nullable String scriptPath;
    @Nullable ProofScript inlineScript;
}


/**
 * Represents a proof script (list of commands).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * proof_script: (proof_script_command)* EOF;
 * }</pre>
 */

class ProofScript {
    List<ProofScriptCommand> commands;
}


/**
 * Represents a proof script command parameter.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * proof_script_param: (ident EQUALS)? expression;
 * }</pre>
 */

class ProofScriptParameter {
    @Nullable String name;
    Object expression;
}


/**
 * Represents a proxy sort declaration.
 * Corresponds to the grammar rule for PROXY kind in one_sort_decl.
 */

class ProxySortDecl {
    @Nullable String docComment;
    List<String> sortNames;
    KeyJavaType javaType;


}


/**
 * Represents a quantifier term (forall/exists).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * quantifier_term: (FORALL | EXISTS) bound_variables DOT term;
 * }</pre>
 */

class QuantifierTerm {
    boolean isUniversal;
    BoundVariables variables;
    Term body;


}


/**
 * Represents replace-with clause in taclet.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * replace_with: term | LPAREN seq SEMI seq RPAREN;
 * }</pre>
 */

class ReplaceWith {
    @Nullable Term term;
    @Nullable Seq antecedent;
    @Nullable Seq succulent;
}


/**
 * Represents a ruleset declaration.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * ruleset_decl: doc=DOC_COMMENT? name=simple_ident (COLON parent_rules+=simple_ident (COMMA parent_rules+=simple_ident)*)? SEMI;
 * }</pre>
 */

class RulesetDecl {
    @Nullable String docComment;
    SimpleIdentDots name;
    List<SimpleIdentDots> parentRules;

}

/**
 * Represents ruleset declarations.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * ruleset_decls: RULESET LBRACE ruleset_decl* RBRACE;
 * }</pre>
 */

class RulesetDecls {
    List<RulesetDecl> decls;

}


/**
 * Represents a rule or axiom.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * rules_or_axioms: (name=rule_name (LPAREN term RPAREN)? | AXIOM) COLON formula (WHEN formula)? (RULESET simple_ident_comma_list)?;
 * }</pre>
 */

class RulesOrAxioms {
    @Nullable String name;
    @Nullable Term condition;
    boolean isAxiom;
    Formula formula;
    @Nullable Formula whenCondition;
    List<String> rulesetNames;


}


/**
 * Represents schema modifiers.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * schema_modifiers: LBRACKET opts = simple_ident_comma_list RBRACKET;
 * }</pre>
 */

class SchemaModifiers {
    List<String> options;
}


/**
 * Represents a schema variable declaration.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * schema_var_decl: kind IDENT;
 * }</pre>
 */

class SchemaVarDecl {
    String name;
    String kind;


}


/**
 * Represents schema variable declarations.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * schema_var_decls: SCHEMAVARIABLES LBRACE (one_schema_var_decl SEMI)* RBRACE;
 * }</pre>
 */

class SchemaVarDecls {
    List<OneSchemaVarDecl> decls;

}

/**
 * Represents a semi-sequent with antecedent and succulent.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * semi_sequent: ante=seq SEMI succ=seq;
 * }</pre>
 */

class SemiSequent {
    Seq antecedent;
    Seq succulent;
}


/**
 * Represents a sequence of terms (antecedent or succulent).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * seq: term (COMMA term)*;
 * }</pre>
 */

class Seq {
    List<Term> terms;

}


/**
 * Represents a simple identifier with dots (qualified name).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * simple_ident_dots: ident+=simple_ident (DOT ident+=simple_ident)*;
 * }</pre>
 */

class SimpleIdentDots {
    String fullName;


}


/**
 * Represents sort declarations.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * sort_decls: SORTS LBRACE (one_sort_decl)* RBRACE;
 * }</pre>
 */

class SortDecls {
    List<OneSortDecl> sortDecls;

}


/**
 * Represents a sort identifier.
 * Corresponds to: id=simple_ident_dots formal_sort_args? (EMPTYBRACKETS)*;
 *
 * @author Cline
 * @version 1.0
 */

class SortId {
    List<String> parts;
    @Nullable FormalSortArgs formalArgs;
    int arrayDimensions;


}


/**
 * Represents a string literal.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * string_literal: STRING_LITERAL;
 * }</pre>
 */

class StringLiteral extends Literals {
    String value;
}


/**
 * Represents a strong arithmetic term with one operand (*, /, %).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * strong_arith_term1: (MULT | DIV | MOD) term;
 * }</pre>
 */

class StrongArithTerm1 {
    enum Op {MUL, DIV, MOD}

    Term operand;
    Op operator;


}


/**
 * Represents a strong arithmetic term with two operands (*, /, %).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * strong_arith_term2: left=term (MULT | DIV | MOD) right=term;
 * }</pre>
 */

class StrongArithTerm2 {
    enum Op {MUL, DIV, MOD}

    Term left;
    Term right;
    Op operator;


}


/**
 * Stub AST node classes for remaining KeY grammar constructs.
 * These are placeholder implementations that can be expanded as needed.
 *
 * @author Cline
 * @version 1.0
 */

class StubAstNodes {

    // ==================== Declaration Stubs ====================

    /**
     * Include statement declaration
     */
    static class IncludeStatement {
        boolean isLDTs;
        List<OneInclude> includes;


    }

    static class OneInclude {
        @Nullable String absFile;
        @Nullable String relFile;


    }

    /**
     * Options choice declaration
     */
    static class OptionsChoice {
        List<ActivatedChoice> choices;
    }

    static class ActivatedChoice {
        String category;
        String choice;
    }

    /**
     * Option declarations
     */
    static class OptionDecls {
        List<Choice> choices;


    }

    static class Choice {
        List<String> docComments;
        String category;
        List<OptionDecl> options;


    }

    static class OptionDecl {
        @Nullable String docComment;
        List<String> choices;


    }

    /**
     * Sort declarations
     */
    static class SortDecls {
        List<OneSortDecl> sorts;


    }

    static class OneSortDecl {
        enum SortKind {GENERIC, PROXY, ABSTRACT, ALIAS}

        SortKind kind;
        @Nullable String docComment;
        List<String> sortIds;
        @Nullable String extendsSorts;
        @Nullable String aliasTarget;


    }

    /**
     * Program variable declarations
     */
    static class ProgVarDecls {
        List<ProgVarDecl> variables;


    }

    static class ProgVarDecl {
        String type;
        List<String> names;


    }

    /**
     * Schema variable declarations
     */
    static class SchemaVarDecls {
        List<OneSchemaVarDecl> schemaVars;


    }

    static class OneSchemaVarDecl {
        enum SchemaKind {MODAL_OPERATOR, PROGRAM, FORMULA, TERMLABEL, UPDATE, SKOLEM_FORMULA, TERM_VAR}

        SchemaKind kind;
        String name;
        @Nullable SortId sort;


    }

    static class SchemaModifiers {
        List<String> options;


    }

    /**
     * Predicate declarations
     */
    static class PredDecls {
        List<PredDecl> predicates;


    }

    static class PredDecl {
        @Nullable String docComment;
        String name;
        List<SortId> argSorts;


    }

    /**
     * Function declarations
     */
    static class FuncDecls {
        List<FuncDecl> functions;


    }

    static class FuncDecl {
        @Nullable String docComment;
        boolean unique;
        SortId returnType;
        String name;
        List<SortId> argSorts;


    }

    /**
     * Transform declarations
     */
    static class TransformDecls {
        List<TransformDecl> transforms;


    }

    static class TransformDecl {
        @Nullable String docComment;
        @Nullable SortId returnType;
        boolean returnsFormula;
        String name;
        List<Object> argSorts;


        boolean returnsFormula() {
            return returnsFormula;
        }
    }

    /**
     * Datatype declarations
     */
    static class DatatypeDecls {
        List<DatatypeDecl> datatypes;


    }

    static class DatatypeDecl {
        @Nullable String docComment;
        String name;
        List<DatatypeConstructor> constructors;


    }

    static class DatatypeConstructor {
        String name;
        List<String> argSorts;
        List<String> argNames;


    }

    /**
     * Ruleset declarations
     */
    static class RulesetDecls {
        List<String> rulesets;


    }

    /**
     * Contracts
     */
    static class Contracts {
        List<OneContract> contracts;


    }

    /**
     * Invariants
     */
    static class Invariants {
        OneBoundVariable selfVar;
        List<OneInvariant> invariants;


    }

    /**
     * Rules or Axioms
     */
    static class RulesOrAxioms {
        @Nullable String docComment;
        boolean isRules;
        @Nullable OptionList options;
        List<Taclet> taclets;


    }

    // ==================== Taclet Support Classes ====================


    static class OptionExpr {
        enum OpKind {AND, OR, NOT, PROP}

        OpKind kind;
        @Nullable OptionExpr left;
        @Nullable OptionExpr right;
        @Nullable String propCategory;
        @Nullable String propValue;


    }

    static class Seq {
        SemiSequent antecedent;
        SemiSequent succedent;


    }

    static class TermOrSeq {
        @Nullable Term term;
        @Nullable Seq seq;


    }

    static class SemiSequent {
        List<Term> terms;


    }

    static class GoalSpecs {
        boolean closeGoal;
        List<GoalSpecWithOption> specs;


    }

    static class GoalSpecWithOption {
        @Nullable OptionList options;
        GoalSpec spec;


    }

    static class GoalSpec {
        @Nullable String name;
        @Nullable String tag;
        @Nullable ReplaceWith replaceWith;
        @Nullable Add add;
        @Nullable AddRules addRules;
        @Nullable AddProgVars addProgVars;


    }

    static class ReplaceWith {
        TermOrSeq termOrSeq;


    }

    static class Add {
        Seq seq;


    }

    static class AddRules {
        List<Taclet> taclets;


    }

    static class AddProgVars {
        List<String> varIds;


    }

    static class Modifiers {
        List<String> rulesets;
        boolean nonInteractive;
        @Nullable String displayName;
        @Nullable String helpText;
        @Nullable Triggers triggers;


    }

    static class Triggers {
        String id;
        Term triggerTerm;
        List<Term> avoidTerms;


    }

    static class VarexpList {
        List<Varexp> varexps;


    }

    static class Varexp {
        boolean negated;
        String varExpId;
        List<String> parameters;
        List<Object> arguments;


    }


    // ==================== Term Support Classes ====================

    static class Label {
        List<SingleLabel> labels;


    }

    static class SingleLabel {
        @Nullable String name;
        boolean isStar;
        List<String> params;


    }

    static class LocsetTerm {
        List<LocationTerm> locations;


    }

    static class LocationTerm {
        Term obj;
        Term field;


    }

    static class AccessTerm {
        @Nullable SortId qualifier;
        String firstName;
        @Nullable FormalSortArgs formalArgs;
        @Nullable Call call;
        List<Attribute> attributes;


    }

    static class Call {
        @Nullable BoundVariables boundVars;
        List<Term> args;


    }

    static class Attribute {
        enum AttrKind {STAR, SIMPLE, COMPLEX}

        AttrKind kind;
        @Nullable String id;
        @Nullable SortId sort;
        @Nullable Call call;
        @Nullable BracketTerm heap;


    }

    static class Abbreviation {
        String name;


    }

    static class IfThenElseTerm {
        Term cond;
        Term thenT;
        Term elseT;


    }

    static class IfExThenElseTerm {
        BoundVariables exVars;
        Term cond;
        Term thenT;
        Term elseT;


    }

    static class BracketTerm {
        Term primitive;
        List<BracketSuffixHeap> suffixes;
        List<Attribute> attributes;


    }

    static class BracketSuffixHeap {
        BraceSuffix braceSuffix;
        @Nullable BracketTerm heap;


    }

    static class BraceSuffix {
        enum SuffixKind {UPDATE, CALL, STAR, INDEX}

        SuffixKind kind;
        @Nullable Term target;
        @Nullable Term value;
        @Nullable String id;
        List<Term> args;
        @Nullable Term indexTerm;
        @Nullable Term rangeTo;


    }

    // ==================== Proof Script Classes ====================

    static class ProofScript {
        List<ProofScriptCommand> commands;


    }

    static class ProofScriptCommand {
        String cmd;
        List<ProofScriptParameter> parameters;


    }

    // ==================== Configuration Classes ====================

    static class ConfigurationFile {
        List<CValue> values;


    }

    static class CKV {
        @Nullable String docComment;
        CKey key;
        CValue value;


    }
}


/**
 * Represents a substitution term (term[subst]).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * substitution_term: term LBRACKET subst RBRACKET;
 * }</pre>
 */

class SubstitutionTerm {
    Term term;
    Term substitution;


}


/**
 * Represents a taclet (KeY's rule specification language).
 * Corresponds to the grammar rule: taclet
 *
 * @author Cline
 * @version 1.0
 */

class Taclet {
    @Nullable String docComment;
    boolean isLemma;
    String name;
    @Nullable OptionList options;
    List<SchemaVarDecl> schemaVars;
    @Nullable Seq assumes;
    @Nullable TermOrSeq find;
    List<String> findModifiers;
    List<VarexpList> varConds;
    GoalSpecs goalSpecs;
    Modifiers modifiers;


}


/**
 * Represents a term in KeY logic.
 * Terms can be simple (literals, variables) or complex (quantified formulas, modalities, etc.)
 *
 * @author Cline
 * @version 1.0
 */

class Term {
    enum TermType {
        PARALLEL, ELEMENTARY_UPDATE, EQUIVALENCE, IMPLICATION, DISJUNCTION, CONJUNCTION, NEGATION, QUANTIFIER, MODALITY, EQUALITY, COMPARISON, WEAK_ARITH, STRONG_ARITH_1, STRONG_ARITH_2, UPDATE, SUBSTITUTION, CAST, UNARY_MINUS, BRACKET, IF_THEN_ELSE, IF_EX_THEN_ELSE, LOCATION, LOCSET, ACCESS, ABBREVIATION, LITERAL
    }

    TermType type;
    String operator;
    @Nullable Term left;
    @Nullable Term right;
    @Nullable Term[] children;
    @Nullable BoundVariables boundVariables;
    @Nullable Label label;


}


/**
 * Represents either a term or a sequence (for taclet find clauses).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * term_or_seq: term | LPAREN seq SEMI seq RPAREN;
 * }</pre>
 */

class TermOrSeq {
    @Nullable Term term;
    @Nullable Seq antecedent;
    @Nullable Seq succulent;
}


/**
 * Represents a transformer declaration.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * transform_decl: doc=DOC_COMMENT? (retSort = sortId | FORMULA) trans_name=funcpred_name argSorts=arg_sorts_or_formula SEMI;
 * }</pre>
 */

class TransformDecl {
    @Nullable String docComment;
    @Nullable SortId returnSort;
    boolean isFormula;
    FuncPredName name;
    ArgSortsOrFormula argSorts;
}


/**
 * Represents transformer declarations.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * transform_decls: TRANSFORMERS LBRACE (transform_decl)* RBRACE;
 * }</pre>
 */

class TransformDecls {
    List<TransformDecl> decls;

}


/**
 * Represents triggers clause in taclet.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * triggers: LBRACE term (COMMA term)* RBRACE;
 * }</pre>
 */

class Triggers {
    List<Term> terms;

}


/**
 * Represents a unary minus term (-term).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * unary_minus_term: MINUS term;
 * }</pre>
 */

class UnaryMinusTerm {
    Term operand;


}


/**
 * Represents an update term (sequential composition).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * update_term: LBRACE elementary_update_term (SEMI elementary_update_term)* RBRACE;
 * }</pre>
 */

class UpdateTerm {
    java.util.List<ElementaryUpdateTerm> updates;

}


/**
 * Represents a variable expression (name and type).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * varexp: ident COLON keyjavatype;
 * }</pre>
 */

class Varexp {
    String name;
    KeyJavaType type;
}


/**
 * Represents a list of variable expressions.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * varexp_list: varexp (COMMA varexp)*;
 * }</pre>
 */

class VarexpList {
    List<Varexp> items;

}


/**
 * Represents a weak arithmetic term (+, -).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * weak_arith_term: left=term (PLUS | MINUS) right=term;
 * }</pre>
 */

class WeakArithTerm {
    enum Op {ADD, SUB}

    Term left;
    Term right;
    Op operator;


}


/**
 * Represents where-to-bind clause.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * where_to_bind: LBRACE b+=(TRUE | FALSE) (COMMA b+=(TRUE | FALSE))* RBRACE;
 * }</pre>
 */
class WhereToBind {
    List<Boolean> bindValues;
}
/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg;

import de.uka.ilkd.key.peg.ast.*;
import org.parboiled.BaseParser;
import org.parboiled.Rule;
import org.parboiled.annotations.BuildParseTree;
import org.parboiled.support.Position;

import java.util.ArrayList;
import java.util.List;

/**
 * PEG-based parser for KeY specification files using parboiled-java.
 * This parser is generated from the ANTLR4 grammar files KeYLexer.g4 and KeYParser.g4.
 *
 * @author Cline
 * @version 1.0
 */
@BuildParseTree
@SuppressWarnings("all")
public class KeYParboiledParser extends BaseParser<Object> {

    // ==================== Lexer Rules (Terminals) ====================

    /**
     * Match a DOC_COMMENT: /*! ... *\/
     */
    public Rule DocComment() {
        return Sequence(
                String("/*!"),
                ZeroOrMore(FirstOf(
                        Sequence(TestNot(String("*/")), ANY),
                        Sequence(String("*/"), ANY)  // Allow */ inside if escaped
                )),
                String("*/"),
                push(new String(match())));
    }

    /**
     * Match an IDENT: letter followed by letters, digits, underscore, hash, or dollar
     */
    public Rule Ident() {
        return Sequence(
                FirstOf(CharRange('a', 'z'),
                        CharRange('A', 'Z'), Ch('_')),
                ZeroOrMore(FirstOf(
                        CharRange('a', 'z'), CharRange('A', 'Z'),
                        CharRange('0', '9'), Ch('_'), Ch('#'), Ch('$')
                )),
                push(new String(match()))
        );
    }

    /**
     * Match a STRING_LITERAL: "..." with escape support
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * STRING_LITERAL: '"' ('\\' ['"\\nrtbfu] | ~['"\\])* '"';
     * }</pre>
     */
    public Rule StringLiteral() {
        return Sequence(
                Ch('"'),
                ZeroOrMore(FirstOf(
                        Sequence(Ch('\\'), FirstOf(Ch('\\'), Ch('"'), Ch('n'), Ch('r'), Ch('t'), Ch('b'), Ch('f'), Ch('u'))),
                        Sequence(TestNot(FirstOf(Ch('"'), Ch('\\'))), ANY)
                )),
                Ch('"'),
                push(new String(match()))
        );
    }

    /**
     * Match an INT_LITERAL
     */
    public Rule IntLiteral() {
        return Sequence(
                FirstOf(
                        Sequence(Ch('0'), FirstOf(
                                Sequence(Ch('b'), OneOrMore(FirstOf(Ch('0'), Ch('1'), Ch('_')))),
                                Sequence(Ch('x'), OneOrMore(FirstOf(CharRange('0', '9'), CharRange('a', 'f'), CharRange('A', 'F'), Ch('_'))))
                        )),
                        (OneOrMore(FirstOf(CharRange('0', '9'), Ch('_'))))
                ),
                Optional(FirstOf(Ch('l'), Ch('L'))),
                push(new String(match()))
        );
    }

    /**
     * Match FLOAT_LITERAL, DOUBLE_LITERAL, REAL_LITERAL
     */
    public Rule FloatNum() {
        return Sequence(
                Optional(Ch('-')),
                FirstOf(
                        Sequence(OneOrMore(Digit()), Optional(Sequence(Ch('.'), ZeroOrMore(Digit()))), Optional(ExpSuffix())),
                        Sequence(Ch('.'), OneOrMore(Digit()), Optional(ExpSuffix()))
                ),
                Optional(FirstOf(
                        Sequence(FirstOf(Ch('f'), Ch('D')), push("float")),
                        Sequence(FirstOf(Ch('d'), Ch('D')), push("double")),
                        Sequence(Optional(FirstOf(Ch('r'), Ch('R'))), push("real"))
                ))
        );
    }

    public Rule ExpSuffix() {
        return Sequence(
                FirstOf(Ch('e'), Ch('E')),
                Optional(FirstOf(Ch('+'), Ch('-'))),
                OneOrMore(Digit()));
    }

    public Rule Digit() {
        return CharRange('0', '9');
    }

    /**
     * Match CHAR_LITERAL with escape support.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * CHAR_LITERAL: '\'' ('\\' ['"\\nrtbfu] | ~[''\\]) '\'';
     * }</pre>
     */
    public Rule CharLiteral() {
        return Sequence(
                Ch('\''),
                FirstOf(
                        CharRange(' ', '&'),
                        CharRange('(', '['),
                        CharRange(']', '~'),
                        Sequence(Ch('\\'), FirstOf(Ch('\''), Ch('\\'), Ch('n'), Ch('r'), Ch('t'), Ch('b'), Ch('f'), Ch('"'), Ch('u')))
                ),
                Ch('\''),
                push(new String(match()))
        );
    }

    // ==================== Keywords ====================

    public Rule KwSorts() {
        return String("\\sorts");
    }

    public Rule KwGeneric() {
        return String("\\generic");
    }

    public Rule KwProxy() {
        return String("\\proxy");
    }

    public Rule KwExtends() {
        return String("\\extends");
    }

    public Rule KwOneof() {
        return String("\\oneof");
    }

    public Rule KwAbstract() {
        return String("\\abstract");
    }

    public Rule KwAlias() {
        return String("\\alias");
    }

    public Rule KwSchemaVariables() {
        return String("\\schemaVariables");
    }

    public Rule KwSchemaVar() {
        return String("\\schemaVar");
    }

    public Rule KwModalOperator() {
        return String("\\modalOperator");
    }

    public Rule KwProgram() {
        return String("\\program");
    }

    public Rule KwFormula() {
        return String("\\formula");
    }

    public Rule KwTerm() {
        return String("\\term");
    }

    public Rule KwUpdate() {
        return String("\\update");
    }

    public Rule KwVariables() {
        return String("\\variables");
    }

    public Rule KwVariable() {
        return String("\\variable");
    }

    public Rule KwSkolemTerm() {
        return String("\\skolemTerm");
    }

    public Rule KwSkolemFormula() {
        return String("\\skolemFormula");
    }

    public Rule KwTermlabel() {
        return String("\\termlabel");
    }

    public Rule KwModifiable() {
        return String("\\modifiable");
    }

    public Rule KwProgramVariables() {
        return String("\\programVariables");
    }

    public Rule KwPredicates() {
        return String("\\predicates");
    }

    public Rule KwFunctions() {
        return String("\\functions");
    }

    public Rule KwDatatypes() {
        return String("\\datatypes");
    }

    public Rule KwTransformers() {
        return String("\\transformers");
    }

    public Rule KwUnique() {
        return String("\\unique");
    }

    public Rule KwRules() {
        return String("\\rules");
    }

    public Rule KwAxioms() {
        return String("\\axioms");
    }

    public Rule KwProblem() {
        return String("\\problem");
    }

    public Rule KwChooseContract() {
        return String("\\chooseContract");
    }

    public Rule KwProofObligation() {
        return String("\\proofObligation");
    }

    public Rule KwProof() {
        return String("\\proof");
    }

    public Rule KwProofScript() {
        return String("\\proofScript");
    }

    public Rule KwContracts() {
        return String("\\contracts");
    }

    public Rule KwInvariants() {
        return String("\\invariants");
    }

    public Rule KwInclude() {
        return String("\\include");
    }

    public Rule KwIncludeLDTs() {
        return String("\\includeLDTs");
    }

    public Rule KwClasspath() {
        return String("\\classpath");
    }

    public Rule KwBootclasspath() {
        return String("\\bootclasspath");
    }

    public Rule KwJavaSource() {
        return String("\\javaSource");
    }

    public Rule KwWithOptions() {
        return String("\\withOptions");
    }

    public Rule KwOptionsDecl() {
        return String("\\optionsDecl");
    }

    public Rule KwSettings() {
        return String("\\settings");
    }

    public Rule KwProfile() {
        return String("\\profile");
    }

    public Rule KwHeuristicsDecl() {
        return String("\\heuristicsDecl");
    }

    public Rule KwLemma() {
        return String("\\lemma");
    }

    public Rule KwHeuristics() {
        return String("\\heuristics");
    }

    public Rule KwFind() {
        return String("\\find");
    }

    public Rule KwAdd() {
        return String("\\add");
    }

    public Rule KwAssumes() {
        return String("\\assumes");
    }

    public Rule KwReplaceWith() {
        return String("\\replacewith");
    }

    public Rule KwAddRules() {
        return String("\\addrules");
    }

    public Rule KwAddProgVars() {
        return String("\\addprogvars");
    }

    public Rule KwTrigger() {
        return String("\\trigger");
    }

    public Rule KwAvoid() {
        return String("\\avoid");
    }

    public Rule KwClosegoal() {
        return String("\\closegoal");
    }

    public Rule KwNoninteractive() {
        return String("\\noninteractive");
    }

    public Rule KwDisplayname() {
        return String("\\displayname");
    }

    public Rule KwHelptext() {
        return String("\\helptext");
    }

    public Rule KwTrue() {
        return fromStringLiteral("true");
    }

    public Rule KwFalse() {
        return fromStringLiteral("false");
    }

    public Rule KwForall() {
        return FirstOf(fromStringLiteral("\\forall "), Ch('\u2200'));
    }

    public Rule KwExists() {
        return FirstOf(fromStringLiteral("\\exists"), Ch('\u2203'));
    }

    public Rule KwSubst() {
        return fromStringLiteral("\\subst");
    }

    public Rule KwIf() {
        return fromStringLiteral("\\if");
    }

    public Rule KwIfEx() {
        return fromStringLiteral("\\ifEx");
    }

    public Rule KwThen() {
        return fromStringLiteral("\\then");
    }

    public Rule KwElse() {
        return fromStringLiteral("\\else");
    }

    public Rule KwFree() {
        return fromStringLiteral("\\free");
    }

    public Rule KwVarcond() {
        return fromStringLiteral("\\varcond");
    }

    // ==================== Operators ====================

    public Rule OpSemi() {
        return Ch(';');
    }

    public Rule OpSlash() {
        return Ch('/');
    }

    public Rule OpColon() {
        return Ch(':');
    }

    public Rule OpDoubleColon() {
        return fromStringLiteral("::");
    }

    public Rule OpAssign() {
        return fromStringLiteral(":=");
    }

    public Rule OpDot() {
        return Ch('.');
    }

    public Rule OpDotRange() {
        return fromStringLiteral("..");
    }

    public Rule OpComma() {
        return Ch(',');
    }

    public Rule OpLParen() {
        return Ch('(');
    }

    public Rule OpRParen() {
        return Ch(')');
    }

    public Rule OpLBrace() {
        return Ch('{');
    }

    public Rule OpRBrace() {
        return Ch('}');
    }

    public Rule OpLBracket() {
        return Ch('[');
    }

    public Rule OpRBracket() {
        return Ch(']');
    }

    public Rule OpEmptyBrackets() {
        return fromStringLiteral("[]");
    }

    public Rule OpAt() {
        return Ch('@');
    }

    public Rule OpParallel() {
        return fromStringLiteral("||");
    }

    public Rule OpOr() {
        return FirstOf(Ch('|'), Ch('\u2228'));
    }

    public Rule OpAnd() {
        return FirstOf(Ch('&'), Ch('\u2227'));
    }

    public Rule OpNot() {
        return FirstOf(Ch('!'), Ch('\u00AC'));
    }

    public Rule OpImp() {
        return FirstOf(String("->"), Ch('\u2192'));
    }

    public Rule OpEquals() {
        return Ch('=');
    }

    public Rule OpNotEquals() {
        return FirstOf(String("!="), Ch('\u2260'));
    }

    public Rule OpSeqArrow() {
        return FirstOf(String("==>"), Ch('\u27F9'));
    }

    public Rule OpEqv() {
        return FirstOf(String("<->"), Ch('\u2194'));
    }

    public Rule OpLess() {
        return Ch('<');
    }

    public Rule OpLessEqual() {
        return FirstOf(String("<="), Ch('\u2264'));
    }

    public Rule OpGreater() {
        return Ch('>');
    }

    public Rule OpGreaterEqual() {
        return FirstOf(String(">="), Ch('\u2265'));
    }

    public Rule OpOpenTypeParams() {
        return String("<[");
    }

    public Rule OpCloseTypeParams() {
        return String("]>");
    }

    public Rule OpPlus() {
        return Ch('+');
    }

    public Rule OpMinus() {
        return Ch('-');
    }

    public Rule OpStar() {
        return Ch('*');
    }

    public Rule OpPercent() {
        return Ch('%');
    }

    // ==================== Whitespace and Comments ====================

    public Rule WS() {
        return (
                OneOrMore(FirstOf(
                        CharRange(' ', '\t'), Ch('\n'), Ch('\r'), Ch('\u00a0')
                ))).suppressNode();
    }

    /**
     * Matches single-line comments (// ...).
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * SL_COMMENT: '//' ~[\r\n]* ('\r'? '\n')?;
     * }</pre>
     */
    public Rule SLComment() {
        return Sequence(
                String("//"),
                ZeroOrMore(TestNot(FirstOf(Ch('\n'), EOI)), ANY),
                FirstOf(Ch('\n'), EOI)
        ).suppressNode();
    }

    // ==================== Parser Rules ====================

    /**
     * Parses a KeY specification file.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * file: DOC_COMMENT* (profile? preferences? decls problem? proof?) EOF;
     * }</pre>
     */
    public Rule File() {
        List<String> docComments = new ArrayList<>();
        Profile profile = null;
        Preferences preferences = null;
        DeclList decls = null;
        Problem problem = null;
        Proof proof = null;

        Position start = getCurrentPosition();

        return Sequence(
                ZeroOrMore(Sequence(DocComment(), push(match()))),
                Optional(Profile()),
                Optional(Preferences()),
                Decls(),
                Optional(this.Problem()),
                Optional(Proof()),
                EOI
        );
        /*setReturnValue(new File(
                        start.line, start.column,
                        getEndLine(), getEndColumn(),
                        docComments, profile, preferences,
                        Values.value(decls), problem, proof
                ))
         */
    }

    /**
     * Parses a list of declarations.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * decls:
     *   ( bootClassPath
     *   | stlist=classPaths
     *   | string=javaSource
     *   | one_include_statement
     *   | options_choice
     *   | option_decls
     *   | sort_decls
     *   | prog_var_decls
     *   | schema_var_decls
     *   | pred_decls
     *   | func_decls
     *   | transform_decls
     *   | datatype_decls
     *   | ruleset_decls
     *   | contracts
     *   | invariants
     *   | rulesOrAxioms
     *   )*
     * ;
     * }</pre>
     */
    public Rule Decls() {
        return
                ZeroOrMore(FirstOf(
                                BootClassPath(),
                                ClassPaths(),
                                JavaSource(),
                                OneIncludeStatement(),
                                OptionsChoice(),
                                OptionDecls(),
                                SortDecls(),
                                ProgVarDecls(),
                                SchemaVarDecls(),
                                PredDecls(),
                                FuncDecls(),
                                TransformDecls(),
                                DatatypeDecls(),
                                RulesetDecls(),
                                Contracts(),
                                Invariants(),
                                RulesOrAxioms()
                        )
                );
    }

    // ==================== Include Statements ====================

    /**
     * Parses an include statement.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * one_include_statement:
     *   (INCLUDE | INCLUDELDTS)
     *   one_include (COMMA one_include)* SEMI
     * ;
     * }</pre>
     */
    public Rule OneIncludeStatement() {
        return Sequence(
                FirstOf(KwInclude(), KwIncludeLDTs()),
                OneOrMore(Sequence(OneInclude(), OpComma())),
                OneInclude(),
                OpSemi()
        );
    }

    /**
     * Parses a single include (absolute or relative file).
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * one_include: absfile=IDENT | relfile=string_value;
     * }</pre>
     */
    public Rule OneInclude() {
        return FirstOf(
                Sequence(Ident(), push("absfile")),
                StringValue()
        );
    }

    // ==================== Options ====================

    /**
     * Parses an options choice declaration.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * options_choice: WITHOPTIONS activated_choice (COMMA activated_choice)* SEMI;
     * }</pre>
     */
    public Rule OptionsChoice() {
        return Sequence(
                KwWithOptions(),
                OneOrMore(Sequence(ActivatedChoice(), Optional(OpComma()))),
                OpSemi()
        );
    }

    /**
     * Parses an activated choice (category:choice).
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * activated_choice: cat=IDENT COLON choice_=IDENT;
     * }</pre>
     */
    public Rule ActivatedChoice() {
        return Sequence(
                Ident(), OpColon(), Ident()
        );
    }

    /**
     * Parses option declarations.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * option_decls: OPTIONSDECL LBRACE (choice SEMI)* RBRACE;
     * }</pre>
     */
    public Rule OptionDecls() {
        return Sequence(
                KwOptionsDecl(), OpLBrace(),
                ZeroOrMore(Sequence(Choice(), OpSemi())),
                OpRBrace()
        );
    }

    /**
     * Parses a choice with optional options.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * choice: maindoc+=DOC_COMMENT* category=IDENT (COLON LBRACE optionDecl (COMMA optionDecl)* RBRACE)?;
     * }</pre>
     */
    public Rule Choice() {
        return Sequence(
                ZeroOrMore(DocComment()),
                Ident(),
                Optional(Sequence(
                        OpColon(), OpLBrace(),
                        OneOrMore(Sequence(OptionDecl(), Optional(OpComma()))),
                        OpRBrace()
                ))
        );
    }

    /**
     * Parses an option declaration.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * optionDecl: doc+=DOC_COMMENT? choice_option+=IDENT;
     * }</pre>
     */
    public Rule OptionDecl() {
        return Sequence(
                Optional(DocComment()),
                OneOrMore(Ident())
        );
    }

    // ==================== Sort Declarations ====================

    /**
     * Parses sort declarations.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * sort_decls: SORTS LBRACE (one_sort_decl)* RBRACE;
     * }</pre>
     */
    public Rule SortDecls() {
        return Sequence(
                KwSorts(), OpLBrace(),
                ZeroOrMore(OneSortDecl()),
                OpRBrace()
        );
    }

    /**
     * Parses a single sort declaration.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * one_sort_decl:
     *   doc=DOC_COMMENT?
     *   ( GENERIC  sortIds=simple_ident_dots_comma_list (ONEOF sortOneOf = oneof_sorts)? (EXTENDS sortExt = extends_sorts)? SEMI
     *   | PROXY  sortIds=simple_ident_dots_comma_list (EXTENDS sortExt=extends_sorts)? SEMI
     *   | ABSTRACT? (sortIds=simple_ident_dots_comma_list | parametric_sort_decl) (EXTENDS sortExt=extends_sorts)?  SEMI
     *   | ALIAS simple_ident_dots EQUALS sortId SEMI
     *   )
     * ;
     * }</pre>
     */
    public Rule OneSortDecl() {
        return Sequence(
                Optional(DocComment()),
                FirstOf(
                        GenericSortDecl(),
                        ProxySortDecl(),
                        AbstractSortDecl(),
                        AliasSortDecl()
                )
        );
    }

    /**
     * Parses a generic sort declaration.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * GENERIC sortIds=simple_ident_dots_comma_list (ONEOF sortOneOf = oneof_sorts)? (EXTENDS sortExt = extends_sorts)? SEMI;
     * }</pre>
     */
    public Rule GenericSortDecl() {
        return Sequence(
                KwGeneric(), SimpleIdentDotsCommaList(),
                Optional(OneOfSorts()),
                Optional(ExtendsSorts()),
                OpSemi()
        );
    }

    /**
     * Parses a proxy sort declaration.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * PROXY sortIds=simple_ident_dots_comma_list (EXTENDS sortExt=extends_sorts)? SEMI;
     * }</pre>
     */
    public Rule ProxySortDecl() {
        return Sequence(
                KwProxy(), SimpleIdentDotsCommaList(),
                Optional(ExtendsSorts()),
                OpSemi()
        );
    }

    /**
     * Parses an abstract sort declaration.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * ABSTRACT? (sortIds=simple_ident_dots_comma_list | parametric_sort_decl) (EXTENDS sortExt=extends_sorts)? SEMI;
     * }</pre>
     */
    public Rule AbstractSortDecl() {
        return Sequence(
                Optional(KwAbstract()),
                FirstOf(SimpleIdentDotsCommaList(), ParametricSortDecl()),
                Optional(ExtendsSorts()),
                OpSemi()
        );
    }

    /**
     * Parses an alias sort declaration.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * ALIAS simple_ident_dots EQUALS sortId SEMI;
     * }</pre>
     */
    public Rule AliasSortDecl() {
        return Sequence(
                KwAlias(), SimpleIdentDots(), OpEquals(), SortId(), OpSemi()
        );
    }

    /**
     * Parses a parametric sort declaration.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * parametric_sort_decl: simple_ident_dots formal_sort_param_decls;
     * }</pre>
     */
    public Rule ParametricSortDecl() {
        return Sequence(
                SimpleIdentDots(), FormalSortParamDecls()
        );
    }

    /**
     * Parses a dotted identifier sequence.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * simple_ident_dots: simple_ident (DOT simple_ident)*;
     * }</pre>
     */
    public Rule SimpleIdentDots() {
        return Sequence(
                Ident(),
                ZeroOrMore(Sequence(OpDot(), Ident()))
        );
    }

    /**
     * Parses a comma-separated list of dotted identifiers.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * simple_ident_dots_comma_list: simple_ident_dots (COMMA simple_ident_dots)*;
     * }</pre>
     */
    public Rule SimpleIdentDotsCommaList() {
        return Sequence(
                SimpleIdentDots(),
                ZeroOrMore(Sequence(OpComma(), SimpleIdentDots()))
        );
    }

    /**
     * Parses extends sort clause.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * extends_sorts: sortId (COMMA sortId)*;
     * }</pre>
     */
    public Rule ExtendsSorts() {
        return Sequence(
                SortId(),
                ZeroOrMore(Sequence(OpComma(), SortId()))
        );
    }

    /**
     * Parses one-of sort specification.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * oneof_sorts: LBRACE s = sortId (COMMA s = sortId) * RBRACE;
     * }</pre>
     */
    public Rule OneOfSorts() {
        return Sequence(
                KwOneof(), OpLBrace(),
                SortId(),
                ZeroOrMore(Sequence(OpComma(), SortId())),
                OpRBrace()
        );
    }

    /**
     * Parses formal sort parameter declarations.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * formal_sort_param_decls: OPENTYPEPARAMS formal_sort_param_decl (COMMA formal_sort_param_decl)* CLOSETYPEPARAMS;
     * }</pre>
     */
    public Rule FormalSortParamDecls() {
        return Sequence(
                OpOpenTypeParams(),
                FormalSortParamDecl(),
                ZeroOrMore(Sequence(OpComma(), FormalSortParamDecl())),
                OpCloseTypeParams()
        );
    }

    /**
     * Parses a single formal sort parameter declaration.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * formal_sort_param_decl: (PLUS | MINUS)? simple_ident;
     * }</pre>
     */
    public Rule FormalSortParamDecl() {
        return Sequence(
                Optional(FirstOf(OpPlus(), OpMinus())),
                Ident()
        );
    }

    public Rule SortId() {
        return Sequence(
                SimpleIdentDots(),
                Optional(FormalSortArgs()),
                ZeroOrMore(OpEmptyBrackets())
        );
    }

    public Rule FormalSortArgs() {
        return Sequence(
                OpOpenTypeParams(),
                SortId(),
                ZeroOrMore(Sequence(OpComma(), SortId())),
                OpCloseTypeParams()
        );
    }

    // ==================== Program Variable Declarations ====================

    /**
     * Parses program variable declarations.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * prog_var_decls:
     *   PROGRAMVARIABLES
     *   LBRACE
     *   ( kjt = keyjavatype var_names = simple_ident_comma_list SEMI )*
     *   RBRACE
     * ;
     * }</pre>
     */
    public Rule ProgVarDecls() {
        return Sequence(
                KwProgramVariables(), OpLBrace(),
                ZeroOrMore(Sequence(
                        KeyJavaType(), SimpleIdentCommaList(), OpSemi()
                )),
                OpRBrace()
        );
    }

    /**
     * Parses a Java type in KeY syntax.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * keyjavatype: type = simple_ident_dots (EMPTYBRACKETS)*;
     * }</pre>
     */
    public Rule KeyJavaType() {
        return Sequence(
                SimpleIdentDots(),
                ZeroOrMore(OpEmptyBrackets())
        );
    }

    /**
     * Parses a comma-separated list of identifiers.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * simple_ident_comma_list: id = simple_ident (COMMA id = simple_ident)*;
     * }</pre>
     */
    public Rule SimpleIdentCommaList() {
        return Sequence(
                Ident(),
                ZeroOrMore(Sequence(OpComma(), Ident()))
        );
    }

    // ==================== Schema Variable Declarations ====================

    /**
     * Parses schema variable declarations.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * schema_var_decls: SCHEMAVARIABLES LBRACE (one_schema_var_decl SEMI)* RBRACE;
     * }</pre>
     */
    public Rule SchemaVarDecls() {
        return Sequence(
                KwSchemaVariables(), OpLBrace(),
                ZeroOrMore(Sequence(OneSchemaVarDecl(), OpSemi())),
                OpRBrace()
        );
    }

    /**
     * Parses a single schema variable declaration.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * one_schema_var_decl:
     *   MODALOPERATOR one_schema_modal_op_decl
     * | PROGRAM (schema_modifiers)? id = simple_ident (LBRACKET nameString=simple_ident EQUALS parameter=simple_ident_dots RBRACKET)? ids=simple_ident_comma_list
     * | FORMULA (schema_modifiers)? ids = simple_ident_comma_list
     * | TERMLABEL (schema_modifiers)? ids=simple_ident_comma_list
     * | UPDATE (schema_modifiers)? ids=simple_ident_comma_list
     * | SKOLEMFORMULA (schema_modifiers)? ids=simple_ident_comma_list
     * | (TERM | (VARIABLES | VARIABLE) | SKOLEMTERM) (schema_modifiers)? s=sortId ids=simple_ident_comma_list
     * ;
     * }</pre>
     */
    public Rule OneSchemaVarDecl() {
        return FirstOf(
                ModalOpSchemaVarDecl(),
                ProgramSchemaVarDecl(),
                FormulaSchemaVarDecl(),
                TermLabelSchemaVarDecl(),
                UpdateSchemaVarDecl(),
                SkolemFormulaSchemaVarDecl(),
                TermOrVarSchemaVarDecl()
        );
    }

    /**
     * Parses a modal operator schema variable declaration.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * one_schema_modal_op_decl: (LPAREN sort = sortId RPAREN)? LBRACE ids = simple_ident_comma_list RBRACE id = simple_ident;
     * }</pre>
     */
    public Rule ModalOpSchemaVarDecl() {
        return Sequence(
                KwModalOperator(),
                Optional(Sequence(OpLParen(), SortId(), OpRParen())),
                OpLBrace(), SimpleIdentCommaList(), OpRBrace(), Ident()
        );
    }

    /**
     * Parses a program schema variable declaration.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * PROGRAM (schema_modifiers)? id = simple_ident (LBRACKET nameString=simple_ident EQUALS parameter=simple_ident_dots RBRACKET)? ids=simple_ident_comma_list;
     * }</pre>
     */
    public Rule ProgramSchemaVarDecl() {
        return Sequence(
                KwProgram(),
                Optional(SchemaModifiers()),
                Ident(),
                Optional(Sequence(OpLBracket(), Ident(), OpEquals(), SimpleIdentDots(), OpRBracket())),
                SimpleIdentCommaList()
        );
    }

    /**
     * Parses a formula schema variable declaration.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * FORMULA (schema_modifiers)? ids = simple_ident_comma_list;
     * }</pre>
     */
    public Rule FormulaSchemaVarDecl() {
        return Sequence(
                KwFormula(), Optional(SchemaModifiers()), SimpleIdentCommaList()
        );
    }

    /**
     * Parses a termlabel schema variable declaration.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * TERMLABEL (schema_modifiers)? ids=simple_ident_comma_list;
     * }</pre>
     */
    public Rule TermLabelSchemaVarDecl() {
        return Sequence(
                KwTermlabel(), Optional(SchemaModifiers()), SimpleIdentCommaList()
        );
    }

    /**
     * Parses an update schema variable declaration.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * UPDATE (schema_modifiers)? ids=simple_ident_comma_list;
     * }</pre>
     */
    public Rule UpdateSchemaVarDecl() {
        return Sequence(
                KwUpdate(), Optional(SchemaModifiers()), SimpleIdentCommaList()
        );
    }

    /**
     * Parses a skolem formula schema variable declaration.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * SKOLEMFORMULA (schema_modifiers)? ids=simple_ident_comma_list;
     * }</pre>
     */
    public Rule SkolemFormulaSchemaVarDecl() {
        return Sequence(
                KwSkolemFormula(), Optional(SchemaModifiers()), SimpleIdentCommaList()
        );
    }

    /**
     * Parses a term or variable schema variable declaration.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * (TERM | (VARIABLES | VARIABLE) | SKOLEMTERM) (schema_modifiers)? s=sortId ids=simple_ident_comma_list;
     * }</pre>
     */
    public Rule TermOrVarSchemaVarDecl() {
        return Sequence(
                FirstOf(KwTerm(), KwVariables(), KwVariable(), KwSkolemTerm()),
                Optional(SchemaModifiers()),
                SortId(),
                SimpleIdentCommaList()
        );
    }

    /**
     * Parses schema modifiers.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * schema_modifiers: LBRACKET opts = simple_ident_comma_list RBRACKET;
     * }</pre>
     */
    public Rule SchemaModifiers() {
        return Sequence(
                OpLBracket(), SimpleIdentCommaList(), OpRBracket()
        );
    }

    // ==================== Predicate Declarations ====================

    public Rule PredDecls() {
        return Sequence(
                KwPredicates(), OpLBrace(),
                ZeroOrMore(PredDecl()),
                OpRBrace()
        );
    }

    public Rule PredDecl() {
        return Sequence(
                Optional(DocComment()),
                FuncPredName(),
                Optional(FormalSortParamDecls()),
                Optional(WhereToBind()),
                ArgSorts(),
                OpSemi()
        );
    }

    // ==================== Function Declarations ====================

    public Rule FuncDecls() {
        return Sequence(
                KwFunctions(), OpLBrace(),
                ZeroOrMore(FuncDecl()),
                OpRBrace()
        );
    }

    public Rule FuncDecl() {
        return Sequence(
                Optional(DocComment()),
                Optional(KwUnique()),
                SortId(),
                FuncPredName(),
                Optional(FormalSortParamDecls()),
                Optional(WhereToBind()),
                ArgSorts(),
                OpSemi()
        );
    }

    public Rule FuncPredName() {
        return Sequence(
                Optional(Sequence(SortId(), OpDoubleColon())),
                FirstOf(SimpleIdentDots(), IntLiteral())
        );
    }

    public Rule ArgSorts() {
        return
                Optional(Sequence(
                        OpLParen(), SortId(), ZeroOrMore(Sequence(OpComma(), SortId())), OpRParen()
                ))
                ;
    }

    public Rule WhereToBind() {
        return Sequence(
                OpLBrace(),
                FirstOf(KwTrue(), KwFalse()),
                ZeroOrMore(Sequence(OpComma(), FirstOf(KwTrue(), KwFalse()))),
                OpRBrace()
        );
    }

    // ==================== Transform Declarations ====================

    public Rule TransformDecls() {
        return Sequence(
                KwTransformers(), OpLBrace(),
                ZeroOrMore(TransformDecl()),
                OpRBrace()
        );
    }

    public Rule TransformDecl() {
        return Sequence(
                Optional(DocComment()),
                FirstOf(SortId(), KwFormula()),
                FuncPredName(),
                ArgSortsOrFormula(),
                OpSemi()
        );
    }

    public Rule ArgSortsOrFormula() {
        return (
                Optional(Sequence(
                        OpLParen(),
                        FirstOf(SortId(), KwFormula()),
                        ZeroOrMore(Sequence(OpComma(), FirstOf(SortId(), KwFormula()))),
                        OpRParen()
                ))
        );
    }

    // ==================== Datatype Declarations ====================

    public Rule DatatypeDecls() {
        return Sequence(
                KwDatatypes(), OpLBrace(),
                ZeroOrMore(DatatypeDecl()),
                OpRBrace()
        );
    }

    public Rule DatatypeDecl() {
        return Sequence(
                Optional(DocComment()),
                Optional(KwFree()),
                SimpleIdentDots(),
                Optional(FormalSortParamDecls()),
                OpEquals(),
                DatatypeConstructor(),
                ZeroOrMore(Sequence(OpOr(), DatatypeConstructor())),
                OpSemi()
        );
    }

    public Rule DatatypeConstructor() {
        return Sequence(
                SimpleIdentDots(),
                Optional(Sequence(
                        OpLParen(),
                        Optional(Sequence(
                                SortId(), Ident(),
                                ZeroOrMore(Sequence(OpComma(), SortId(), Ident()))
                        )),
                        OpRParen()
                ))
        );
    }

    // ==================== Ruleset Declarations ====================

    public Rule RulesetDecls() {
        return Sequence(
                KwHeuristicsDecl(), OpLBrace(),
                ZeroOrMore(Sequence(Optional(DocComment()), Ident(), OpSemi())),
                OpRBrace()
        );
    }

    // ==================== Taclet ====================

    public Rule Taclet() {
        return Sequence(
                Optional(DocComment()),
                Optional(KwLemma()),
                Ident(),
                Optional(OptionList()),
                OpLBrace(),
                FirstOf(
                        Term(),
                        Sequence(
                                ZeroOrMore(Sequence(KwSchemaVar(), OneSchemaVarDecl(), OpSemi())),
                                Optional(Sequence(KwAssumes(), OpLParen(), Seq(), OpRParen())),
                                Optional(Sequence(
                                        KwFind(), OpLParen(), TermOrSeq(), OpRParen(),
                                        ZeroOrMore(FirstOf(
                                                fromStringLiteral("\\sameUpdateLevel"),
                                                fromStringLiteral("\\inSequentState"),
                                                fromStringLiteral("\\antecedentPolarity"),
                                                fromStringLiteral("\\succedentPolarity")
                                        ))
                                )),
                                ZeroOrMore(Sequence(KwVarcond(), OpLParen(), VarexpList(), OpRParen())),
                                GoalSpecs(),
                                Modifiers()
                        )
                ),
                OpRBrace()
        );
    }

    public Rule Modifiers() {
        return ZeroOrMore(FirstOf(
                Rulesets(),
                KwNoninteractive(),
                Sequence(KwDisplayname(), StringValue()),
                Sequence(KwHelptext(), StringValue()),
                Triggers()
        ));
    }

    public Rule Seq() {
        return Sequence(
                SemiSequent(), OpSeqArrow(), SemiSequent()
        );
    }

    public Rule TermOrSeq() {
        return
                FirstOf(
                        Sequence(Term(), Optional(FirstOf(
                                Sequence(OpComma(), Seq()),
                                Sequence(OpSeqArrow(), SemiSequent())
                        ))),
                        Sequence(OpSeqArrow(), SemiSequent())
                );
    }

    public Rule SemiSequent() {
        return (
                Optional(Sequence(
                        Term(),
                        ZeroOrMore(Sequence(OpComma(), SemiSequent()))
                ))
        );
    }

    public Rule GoalSpecs() {
        return (
                FirstOf(
                        KwClosegoal(),
                        Sequence(GoalSpecWithOption(), ZeroOrMore(Sequence(OpSemi(), GoalSpecWithOption())))
                )
        );
    }

    public Rule GoalSpecWithOption() {
        return
                FirstOf(
                        Sequence(OptionList(), OpLBrace(), GoalSpec(), OpRBrace()),
                        GoalSpec()
                );
    }

    public Rule GoalSpec() {
        return Sequence(
                Optional(Sequence(StringValue(), Optional(OpLBracket(), SimpleIdentDots(), OpRBracket()), OpColon())),
                FirstOf(
                        Sequence(ReplaceWith(), Optional(Add()), Optional(AddRules()), Optional(AddProgVars())),
                        Sequence(Add(), Optional(AddRules())),
                        AddRules()
                )
        );
    }

    public Rule ReplaceWith() {
        return Sequence(KwReplaceWith(), OpLParen(), TermOrSeq(), OpRParen());
    }

    public Rule Add() {
        return Sequence(KwAdd(), OpLParen(), Seq(), OpRParen());
    }

    public Rule AddRules() {
        return Sequence(KwAddRules(), OpLParen(), TacletList(), OpRParen());
    }

    public Rule AddProgVars() {
        return Sequence(KwAddProgVars(), OpLParen(), PvSet(), OpRParen());
    }

    public Rule TacletList() {
        return Sequence(Taclet(), ZeroOrMore(Sequence(OpComma(), Taclet())));
    }

    public Rule PvSet() {
        return Sequence(Ident(), ZeroOrMore(Sequence(OpComma(), Ident())));
    }

    public Rule Triggers() {
        return Sequence(
                KwTrigger(), OpLBrace(), Ident(), OpRBrace(), Term(),
                Optional(Sequence(KwAvoid(), Term(), ZeroOrMore(Sequence(OpComma(), Term())))),
                OpSemi()
        );
    }

    public Rule VarexpList() {
        return Sequence(Varexp(), ZeroOrMore(Sequence(OpComma(), Varexp())));
    }

    public Rule Varexp() {
        return Sequence(
                Optional(OpNot()),
                VarexpId(),
                Optional(OpLBracket(), Ident(), ZeroOrMore(Sequence(OpComma(), Ident())), OpRBracket()),
                Optional(OpLParen(), VarexpArgument(), ZeroOrMore(Sequence(OpComma(), VarexpArgument())), OpRParen())
        );
    }

    public Rule VarexpId() {
        return FirstOf(
                fromStringLiteral("\\applyUpdateOnRigid"), fromStringLiteral("\\sameObserver"),
                fromStringLiteral("\\dropEffectlessElementaries"), fromStringLiteral("\\dropEffectlessStores"),
                fromStringLiteral("\\differentFields"), fromStringLiteral("\\simplifyIfThenElseUpdate"),
                fromStringLiteral("\\containsAssignment"), fromStringLiteral("\\isEnumType"), fromStringLiteral("\\isThisReference"),
                fromStringLiteral("\\staticMethodReference"), fromStringLiteral("\\isReferenceArray"), fromStringLiteral("\\isArray"),
                fromStringLiteral("\\isArrayLength"), fromStringLiteral("\\isAbstractOrInterface"), fromStringLiteral("\\isFinal"),
                fromStringLiteral("\\enumConstant"), fromStringLiteral("\\final"), fromStringLiteral("\\static"),
                fromStringLiteral("\\isLocalVariable"), fromStringLiteral("\\isObserver"), fromStringLiteral("\\different"),
                fromStringLiteral("\\metaDisjoint"), fromStringLiteral("\\equalUnique"), fromStringLiteral("\\freeLabelIn"),
                fromStringLiteral("\\isConstant"), fromStringLiteral("\\hasLabel"), fromStringLiteral("\\isStaticField"),
                fromStringLiteral("\\isModelField"), fromStringLiteral("\\hasSubFormulas"), fromStringLiteral("\\fieldType"),
                fromStringLiteral("\\new"), fromStringLiteral("\\newTypeOf"), fromStringLiteral("\\newDependingOn"),
                fromStringLiteral("\\newLocalVars"), fromStringLiteral("\\hasElementarySort"), fromStringLiteral("\\same"),
                fromStringLiteral("\\sub"), fromStringLiteral("\\strict"), fromStringLiteral("\\sub"),
                fromStringLiteral("\\disjointModuloNull"), fromStringLiteral("\\notFreeIn"), fromStringLiteral("\\hasSort"),
                fromStringLiteral("\\newLabel"), fromStringLiteral("\\isReference"), fromStringLiteral("\\mayExpandMethod"),
                fromStringLiteral("\\storeTermIn"), fromStringLiteral("\\storeStmtIn"), fromStringLiteral("\\hasInvariant"),
                fromStringLiteral("\\getInvariant"), fromStringLiteral("\\getFreeInvariant"), fromStringLiteral("\\getVariant"),
                fromStringLiteral("\\isLabeled"), fromStringLiteral("\\isInStrictFp")
        );
    }

    public Rule VarexpArgument() {
        return FirstOf(
                Sequence(fromStringLiteral("\\typeof"), OpLParen(), Ident(), OpRParen()),
                Sequence(fromStringLiteral("\\containerType"), OpLParen(), Ident(), OpRParen()),
                Sequence(fromStringLiteral("\\dependingOn"), OpLParen(), Ident(), OpRParen()),
                Term()
        );
    }

    public Rule OptionList() {
        return Sequence(
                OpLParen(),
                Optional(Sequence(OptionExpr(), ZeroOrMore(Sequence(OpComma(), OptionExpr())))),
                OpRParen()
        );
    }

    public Rule OptionExpr() {
        return
                FirstOf(
                        Sequence(OptionExpr(), OpAnd(), OptionExpr()),
                        Sequence(OptionExpr(), OpOr(), OptionExpr()),
                        Sequence(OpNot(), OptionExpr()),
                        Sequence(OpLParen(), OptionExpr(), OpRParen()),
                        Option()
                );
    }

    public Rule Option() {
        return Sequence(Ident(), OpColon(), Ident());
    }

    public Rule Rulesets() {
        return Sequence(
                KwHeuristics(), OpLParen(), Ruleset(), ZeroOrMore(Sequence(OpComma(), Ruleset())), OpRParen()
        );
    }

    public Rule Ruleset() {
        return Ident();
    }

    // ==================== Terms and Formulas ====================

    public Rule Term() {
        return ParallelTerm();
    }

    public Rule ParallelTerm() {
        return Sequence(
                ElementaryUpdateTerm(),
                ZeroOrMore(Sequence(OpParallel(), ElementaryUpdateTerm()))
        );
    }

    public Rule ElementaryUpdateTerm() {
        return Sequence(
                EquivalenceTerm(),
                Optional(Sequence(OpAssign(), EquivalenceTerm()))
        );
    }

    public Rule EquivalenceTerm() {
        return Sequence(
                ImplicationTerm(),
                ZeroOrMore(Sequence(OpEqv(), ImplicationTerm()))
        );
    }

    public Rule ImplicationTerm() {
        return Sequence(
                DisjunctionTerm(),
                Optional(Sequence(OpImp(), ImplicationTerm()))
        );
    }

    public Rule DisjunctionTerm() {
        return Sequence(
                ConjunctionTerm(),
                ZeroOrMore(Sequence(OpOr(), ConjunctionTerm()))
        );
    }

    public Rule ConjunctionTerm() {
        return Sequence(
                Term60(),
                ZeroOrMore(Sequence(OpAnd(), Term60()))
        );
    }

    public Rule Term60() {
        return FirstOf(UnaryFormula(), EqualityTerm());
    }

    public Rule UnaryFormula() {
        return FirstOf(
                Sequence(OpNot(), Term60()),
                Sequence(FirstOf(KwForall(), KwExists()), BoundVariables(), Term60()),
                Sequence(Modality(), Term60())
        );
    }

    public Rule EqualityTerm() {
        return Sequence(
                ComparisonTerm(),
                Optional(Sequence(FirstOf(OpNotEquals(), OpEquals()), ComparisonTerm()))
        );
    }

    public Rule ComparisonTerm() {
        return Sequence(
                WeakArithTerm(),
                Optional(
                        Sequence(
                                FirstOf(OpLess(), OpLessEqual(), OpGreater(), OpGreaterEqual(),
                                        Ch('\u227A'),
                                        Ch('\u220A'),
                                        Ch('\u2286'),
                                        Ch('\u2282'),
                                        Ch('\u2216')),
                                WeakArithTerm()
                        ))
        );
    }

    public Rule WeakArithTerm() {
        return Sequence(
                StrongArithTerm1(),
                ZeroOrMore(Sequence(FirstOf(OpPlus(), OpMinus(), Ch('\u222A'), Ch('\u2229'), Ch('\u2216')), StrongArithTerm1()))
        );
    }

    public Rule StrongArithTerm1() {
        return Sequence(
                StrongArithTerm2(),
                ZeroOrMore(Sequence(OpStar(), StrongArithTerm2()))
        );
    }

    public Rule StrongArithTerm2() {
        return Sequence(
                AtomPrefix(),
                ZeroOrMore(Sequence(FirstOf(OpPercent(), OpSlash()), AtomPrefix()))
        );
    }

    public Rule AtomPrefix() {
        return FirstOf(
                UpdateTerm(),
                SubstitutionTerm(),
                LocsetTerm(),
                CastTerm(),
                UnaryMinusTerm(),
                BracketTerm()
        );
    }

    public Rule UpdateTerm() {
        return Sequence(
                OpLBrace(), ParallelTerm(), OpRBrace(),
                FirstOf(AtomPrefix(), Term60())
        );
    }

    public Rule SubstitutionTerm() {
        return Sequence(
                OpLBrace(), KwSubst(), OneBoundVariable(), OpSemi(), ComparisonTerm(), OpRBrace(),
                FirstOf(AtomPrefix(), Term60())
        );
    }

    public Rule CastTerm() {
        return Sequence(OpLParen(), SortId(), OpRParen(), AtomPrefix());
    }

    public Rule UnaryMinusTerm() {
        return Sequence(OpMinus(), AtomPrefix());
    }

    public Rule BracketTerm() {
        return Sequence(
                PrimitiveLabeledTerm(),
                ZeroOrMore(BracketSuffixHeap()),
                ZeroOrMore(Attribute())
        );
    }

    public Rule BracketSuffixHeap() {
        return Sequence(BraceSuffix(), Optional(OpAt(), BracketTerm()));
    }

    public Rule BraceSuffix() {
        return FirstOf(
                Sequence(OpLBracket(), Term(), OpAssign(), Term(), OpRBracket()),
                Sequence(OpLBracket(), Ident(), ArgumentList(), OpRBracket()),
                Sequence(OpLBracket(), OpStar(), OpRBracket()),
                Sequence(OpLBracket(), Term(), Optional(OpDotRange(), Term()), OpRBracket())
        );
    }

    public Rule Attribute() {
        return FirstOf(
                Sequence(OpDot(), OpStar()),
                Sequence(OpDot(), Ident(), Optional(Call()), Optional(OpAt(), BracketTerm())),
                Sequence(OpDot(), OpLParen(), SortId(), OpDoubleColon(), Ident(), OpRParen(), Optional(Call()), Optional(OpAt(), BracketTerm()))
        );
    }

    public Rule PrimitiveLabeledTerm() {
        return Sequence(PrimitiveTerm(), Optional(String("<<"), Label(), String(">>")));
    }

    Rule WhiteSpace() {
        return OneOrMore(AnyOf(" \t\f"));
    }

    // we redefine the rule creation for string literals to automatically match trailing whitespace if the string
    // literal ends with a space character, this way we don't have to insert extra whitespace() rules after each
    // character or string literal
    @Override
    protected Rule fromStringLiteral(String string) {
        return string.endsWith(" ") ?
                Sequence(String(string.substring(0, string.length() - 1)), WhiteSpace()) :
                String(string);
    }

    public Rule PrimitiveTerm() {
        return FirstOf(
                Sequence(OpLParen(), Term(), OpRParen(), ZeroOrMore(Attribute())),
                IfThenElseTerm(),
                IfExThenElseTerm(),
                Abbreviation(),
                AccessTerm(),
                Literals()
        );
    }

    public Rule Abbreviation() {
        return Sequence(OpAt(), SimpleIdentDots());
    }

    public Rule IfThenElseTerm() {
        return Sequence(
                KwIf(), OpLParen(), Term(), OpRParen(),
                KwThen(), OpLParen(), Term(), OpRParen(),
                KwElse(), OpLParen(), Term(), OpRParen()
        );
    }

    public Rule IfExThenElseTerm() {
        return Sequence(
                KwIfEx(), BoundVariables(),
                OpLParen(), Term(), OpRParen(),
                KwThen(), OpLParen(), Term(), OpRParen(),
                KwElse(), OpLParen(), Term(), OpRParen()
        );
    }

    public Rule AccessTerm() {
        return Sequence(
                Optional(Sequence(SortId(), OpDoubleColon())),
                Ident(),
                Optional(FormalSortArgs()),
                Optional(Call()),
                ZeroOrMore(Attribute())
        );
    }

    public Rule Call() {
        return Sequence(
                Optional(Sequence(OpLBrace(), BoundVariables(), OpRBrace())),
                ArgumentList()
        );
    }

    public Rule ArgumentList() {
        return Sequence(
                OpLParen(),
                Optional(Sequence(Term(), ZeroOrMore(Sequence(OpComma(), Term())))),
                OpRParen()
        );
    }

    public Rule Label() {
        return Sequence(
                SingleLabel(),
                ZeroOrMore(Sequence(OpComma(), SingleLabel()))
        );
    }

    public Rule SingleLabel() {
        return Sequence(
                FirstOf(Ident(), OpStar()),
                Optional(OpLParen(), Optional(Sequence(StringValue(), ZeroOrMore(Sequence(OpComma(), StringValue())))), OpRParen())
        );
    }

    public Rule LocsetTerm() {
        return Sequence(
                OpLBrace(),
                Optional(Sequence(LocationTerm(), ZeroOrMore(Sequence(OpComma(), LocationTerm())))),
                OpRBrace()
        );
    }

    public Rule LocationTerm() {
        return Sequence(OpLParen(), EquivalenceTerm(), OpComma(), EquivalenceTerm(), OpRParen());
    }

    public Rule BoundVariables() {
        return Sequence(
                OneBoundVariable(),
                ZeroOrMore(Sequence(OpComma(), OneBoundVariable())),
                OpSemi()
        );
    }

    public Rule OneBoundVariable() {
        return Sequence(Optional(Sequence(SortId(), WhiteSpace())), Ident());
    }

    public Rule Literals() {
        return FirstOf(
                BooleanLiteral(),
                CharLiteral(),
                IntegerLiteral(),
                FloatLiteral(),
                StringLiteral(),
                EmptySet()
        );
    }

    public Rule BooleanLiteral() {
        return FirstOf(KwTrue(), KwFalse());
    }

    public Rule IntegerLiteral() {
        return IntLiteral();
    }

    public Rule FloatLiteral() {
        return FloatNum();
    }

    public Rule StringValue() {
        return StringLiteral();
    }

    public Rule EmptySet() {
        return FirstOf(Ch('\u2205'), fromStringLiteral("\\emptyset"));
    }

    public Rule Modality() {
        return Sequence(
                fromStringLiteral("\\modality"),
                push("modality")
        );
    }

    // ==================== Contracts and Invariants ====================

    public Rule Contracts() {
        return Sequence(
                KwContracts(), OpLBrace(),
                ZeroOrMore(OneContract()),
                OpRBrace()
        );
    }

    public Rule OneContract() {
        return Sequence(
                SimpleIdentDots(), OpLBrace(),
                Optional(ProgVarDecls()),
                Term(), KwModifiable(), Term(),
                OpRBrace(), OpSemi()
        );
    }

    public Rule Invariants() {
        return Sequence(
                KwInvariants(), OpLParen(), OneBoundVariable(), OpRParen(),
                OpLBrace(),
                ZeroOrMore(OneInvariant()),
                OpRBrace()
        );
    }

    public Rule OneInvariant() {
        return Sequence(
                SimpleIdentDots(), OpLBrace(),
                Term(),
                Optional(Sequence(KwDisplayname(), StringValue())),
                OpRBrace(), OpSemi()
        );
    }

    // ==================== Rules or Axioms ====================

    public Rule RulesOrAxioms() {
        return Sequence(
                Optional(DocComment()),
                FirstOf(KwRules(), KwAxioms()),
                Optional(OptionList()),
                OpLBrace(),
                ZeroOrMore(Sequence(Taclet(), OpSemi())),
                OpRBrace()
        );
    }

    // ==================== File-level declarations ====================

    public Rule BootClassPath() {
        return Sequence(KwBootclasspath(), StringValue(), OpSemi());
    }

    public Rule ClassPaths() {
        return Sequence(KwClasspath(), StringValue(), ZeroOrMore(Sequence(OpComma(), StringValue())), OpSemi());
    }

    public Rule JavaSource() {
        return Sequence(
                KwJavaSource(),
                OneOrMore(FirstOf(StringValue(), OpColon())),
                OpSemi()
        );
    }

    public Rule Profile() {
        return Sequence(KwProfile(), StringValue(), OpSemi());
    }

    public Rule Preferences() {
        return Sequence(
                KwSettings(),
                FirstOf(
                        Sequence(OpLBrace(), Optional(StringValue()), OpRBrace()),
                        CValue()
                )
        );
    }

    // ==================== Problem ====================

    /**
     * Parses a problem declaration.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * problem:
     *   ( PROBLEM LBRACE ( t=termorseq ) RBRACE
     *   | CHOOSECONTRACT (chooseContract=string_value SEMI)?
     *   | PROOFOBLIGATION  (proofObligation=cvalue)? SEMI?
     *   )
     *   proofScriptEntry?
     * ;
     * }</pre>
     */
    public Rule Problem() {
        return Sequence(
                FirstOf(
                        Sequence(KwProblem(), OpLBrace(), TermOrSeq(), OpRBrace()),
                        Sequence(KwChooseContract(), Optional(StringValue()), OpSemi()),
                        Sequence(KwProofObligation(), Optional(CValue()), Optional(OpSemi()))
                ),
                Optional(ProofScriptEntry())
        );
    }

    /**
     * Parses a proof script entry.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * proofScriptEntry: PROOFSCRIPT ( STRING_LITERAL SEMI? | LBRACE proofScript RBRACE );
     * }</pre>
     */
    public Rule ProofScriptEntry() {
        return Sequence(
                KwProofScript(),
                FirstOf(
                        Sequence(StringValue(), Optional(OpSemi())),
                        Sequence(OpLBrace(), ProofScript(), OpRBrace())
                )
        );
    }

    // ==================== Proof ====================

    /**
     * Parses proof section.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * proof: PROOF EOF;
     * }</pre>
     */
    public Rule Proof() {
        return Sequence(KwProof(), EOI);
    }

    // ==================== Proof Script ====================

    public Rule ProofScript() {
        return ZeroOrMore(ProofScriptCommand());
    }

    public Rule ProofScriptCommand() {
        return Sequence(Ident(), ZeroOrMore(ProofScriptParameter()), OpSemi());
    }

    public Rule ProofScriptParameter() {
        return Sequence(
                Optional(Sequence(Optional(OpAt()), Ident(), FirstOf(OpColon(), OpEquals()))),
                ProofScriptExpression()
        );
    }

    public Rule ProofScriptExpression() {
        return FirstOf(
                BooleanLiteral(),
                CharLiteral(),
                IntegerLiteral(),
                FloatLiteral(),
                StringValue(),
                Sequence(OpLParen(), FirstOf(Term(), Seq()), OpRParen()),
                Ident(),
                Abbreviation(),
                Literals(),
                ProofScriptCodeBlock()
        );
    }

    public Rule ProofScriptCodeBlock() {
        return Sequence(OpLBrace(), ProofScript(), OpRBrace());
    }

    // ==================== Configuration ====================

    /**
     * Parses configuration file.
     * <p>
     * Original ANTLR4 grammar rule:
     * <pre>{@code
     * cfile: cvalue* EOF;
     * }</pre>
     */
    public Rule CFile() {
        return Sequence(ZeroOrMore(CValue()), EOI);
    }

    public Rule CKV() {
        return Sequence(Optional(DocComment()), CKey(), OpColon(), CValue());
    }

    public Rule CKey() {
        return FirstOf(Ident(), StringValue());
    }

    public Rule CValue() {
        return FirstOf(
                Sequence(Ident(), push("symbol")),
                Sequence(StringValue(), push("string")),
                Sequence(IntLiteral(), push("int")),
                Sequence(FloatNum(), push("float")),
                Sequence(FirstOf(KwTrue(), KwFalse()), push("bool")),
                Table(),
                ListValue()
        );
    }

    public Rule Table() {
        return Sequence(
                OpLBrace(),
                ZeroOrMore(Sequence(CKV(), Optional(OpComma()))),
                Optional(OpComma()),
                OpRBrace()
        );
    }

    public Rule ListValue() {
        return Sequence(
                OpLBracket(),
                ZeroOrMore(Sequence(CValue(), Optional(OpComma()))),
                Optional(OpComma()),
                OpRBracket()
        );
    }

    // ==================== Helper Methods ====================

    /**
     * Get the current position in the input stream.
     *
     * @return Position object with line and column information
     */
    public Position getCurrentPosition() {
        return getContext().getPosition();
    }

    public int getStartLine() {
        return getCurrentPosition().line;
    }

    public int getStartColumn() {
        return getCurrentPosition().column;
    }

    public int getEndLine() {
        Position pos = getCurrentPosition();
        return pos.line;
    }

    public int getEndColumn() {
        Position pos = getCurrentPosition();
        return pos.column;
    }
}

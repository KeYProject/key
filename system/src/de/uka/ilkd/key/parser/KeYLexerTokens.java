// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.parser;

/**
 * This class provides better literals to the tokens in the keyparser.
 *
 * Error messages read like
 *
 * <pre>
 * mismatched input '}' expecting SEMI
 * </pre>
 *
 * but should better be
 *
 * <pre>
 * mismatched input '}' expecting ';'
 * </pre>
 *
 * In ANTLRv3 this can no longer be achieved using paraphrasing. There this
 * class containing literals for the tokens.
 *
 * <h2>Updating</h2>
 *
 * The content of the {@link #prepareTokens()} method can be either manually
 * created or using "KeYLexerTokensUpdater.g". Proceed as follows (you may have
 * to change paths of course)
 *
 * <pre>
 *   cp KeYLexerTokensUpdater.g $TMPDIR
 *   cp KeYLexer.g $TMPDIR
 *   cp antlr-3.5.1.jar $TMPDIR
 *   cd $TMPDIR
 *   java -jar antlr-3.5.1.jar KeYLexerTokensUpdater.g
 *   javac -cp antlr-3.5.1.jar *.java
 *   java -cp antlr-3.5.1.jar:. KeYLexerTokensUpdaterParser < KeYLexer.g
 * </pre>
 *
 * Paste the output into the method {@link #prepareTokens()}
 *
 * <p>
 * You can also maintain the list manually. If something is missed, the only
 * thing affected are error messages. If a token gets deleted, a syntax error
 * will light up here. Just remove the corresponding line.
 *
 * @author mulbrich
 */

public class KeYLexerTokens {

    private KeYLexerTokens() {
        throw new Error("do not instantiate");
    }

    private static String[] tokenNames;

    public static String[] getTokennames() {
        if(tokenNames == null) {
            prepareTokens();
        }
        return tokenNames;
    }

    private static void prepareTokens() {
        // make local copy first, to make getTokennames reentrant.
        String names[] = KeYParser.tokenNames.clone();
        // ---- begin generated token names ----
        names[KeYParser.SORTS] = "'\\sorts'";
        names[KeYParser.GENERIC] = "'\\generic'";
        names[KeYParser.PROXY] = "'\\proxy'";
        names[KeYParser.EXTENDS] = "'\\extends'";
        names[KeYParser.ONEOF] = "'\\oneof'";
        names[KeYParser.ABSTRACT] = "'\\abstract'";
        names[KeYParser.SCHEMAVARIABLES] = "'\\schemaVariables'";
        names[KeYParser.SCHEMAVAR] = "'\\schemaVar'";
        names[KeYParser.MODALOPERATOR] = "'\\modalOperator'";
        names[KeYParser.PROGRAM] = "'\\program'";
        names[KeYParser.FORMULA] = "'\\formula'";
        names[KeYParser.TERM] = "'\\term'";
        names[KeYParser.UPDATE] = "'\\update'";
        names[KeYParser.VARIABLES] = "'\\variables'";
        names[KeYParser.SKOLEMTERM] = "'\\skolemTerm'";
        names[KeYParser.SKOLEMFORMULA] = "'\\skolemFormula'";
        names[KeYParser.TERMLABEL] = "'\\termlabel'";
        names[KeYParser.MODIFIES] = "'\\modifies'";
        names[KeYParser.PROGRAMVARIABLES] = "'\\programVariables'";
        names[KeYParser.VARCOND] = "'\\varcond'";
        names[KeYParser.APPLY_UPDATE_ON_RIGID] = "'\\applyUpdateOnRigid'";
        names[KeYParser.DEPENDINGON] = "'\\dependingOn'";
        names[KeYParser.DISJOINTMODULONULL] = "'\\disjointModuloNull'";
        names[KeYParser.DROP_EFFECTLESS_ELEMENTARIES] = "'\\dropEffectlessElementaries'";
        names[KeYParser.DROP_EFFECTLESS_STORES] = "'\\dropEffectlessStores'";
        names[KeYParser.SIMPLIFY_IF_THEN_ELSE_UPDATE] = "'\\simplifyIfThenElseUpdate'";
        names[KeYParser.ENUM_CONST] = "'\\enumConstant'";
        names[KeYParser.FREELABELIN] = "'\\freeLabelIn'";
        names[KeYParser.HASSORT] = "'\\hasSort'";
        names[KeYParser.FIELDTYPE] = "'\\fieldType'";
        names[KeYParser.FINAL] = "'\\final'";
        names[KeYParser.ELEMSORT] = "'\\elemSort'";
        names[KeYParser.HASLABEL] = "'\\hasLabel'";
        names[KeYParser.HASSUBFORMULAS] = "'\\hasSubFormulas'";
        names[KeYParser.ISARRAY] = "'\\isArray'";
        names[KeYParser.ISARRAYLENGTH] = "'\\isArrayLength'";
        names[KeYParser.ISCONSTANT] = "'\\isConstant'";
        names[KeYParser.ISENUMTYPE] = "'\\isEnumType'";
        names[KeYParser.ISINDUCTVAR] = "'\\isInductVar'";
        names[KeYParser.ISLOCALVARIABLE] = "'\\isLocalVariable'";
        names[KeYParser.ISOBSERVER] = "'\\isObserver'";
        names[KeYParser.DIFFERENT] = "'\\different'";
        names[KeYParser.METADISJOINT] = "'\\metaDisjoint'";
        names[KeYParser.ISTHISREFERENCE] = "'\\isThisReference'";
        names[KeYParser.DIFFERENTFIELDS] = "'\\differentFields'";
        names[KeYParser.ISREFERENCE] = "'\\isReference'";
        names[KeYParser.ISREFERENCEARRAY] = "'\\isReferenceArray'";
        names[KeYParser.ISSTATICFIELD] = "'\\isStaticField'";
        names[KeYParser.ISSUBTYPE] = "'\\sub'";
        names[KeYParser.EQUAL_UNIQUE] = "'\\equalUnique'";
        names[KeYParser.NEW] = "'\\new'";
        names[KeYParser.NEWLABEL] = "'\\newLabel'";
        names[KeYParser.NOT_] = "'\\not'";
        names[KeYParser.NOTFREEIN] = "'\\notFreeIn'";
        names[KeYParser.SAME] = "'\\same'";
        names[KeYParser.STATIC] = "'\\static'";
        names[KeYParser.STATICMETHODREFERENCE] = "'\\staticMethodReference'";
        names[KeYParser.STRICT] = "'\\strict'";
        names[KeYParser.TYPEOF] = "'\\typeof'";
        names[KeYParser.INSTANTIATE_GENERIC] = "'\\instantiateGeneric'";
        names[KeYParser.SUBST] = "'\\subst'";
        names[KeYParser.IF] = "'\\if'";
        names[KeYParser.IFEX] = "'\\ifEx'";
        names[KeYParser.THEN] = "'\\then'";
        names[KeYParser.ELSE] = "'\\else'";
        names[KeYParser.INCLUDE] = "'\\include'";
        names[KeYParser.INCLUDELDTS] = "'\\includeLDTs'";
        names[KeYParser.CLASSPATH] = "'\\classpath'";
        names[KeYParser.BOOTCLASSPATH] = "'\\bootclasspath'";
        names[KeYParser.NODEFAULTCLASSES] = "'\\noDefaultClasses'";
        names[KeYParser.JAVASOURCE] = "'\\javaSource'";
        names[KeYParser.WITHOPTIONS] = "'\\withOptions'";
        names[KeYParser.OPTIONSDECL] = "'\\optionsDecl'";
        names[KeYParser.KEYSETTINGS] = "'\\settings'";
        names[KeYParser.PROFILE] = "'\\profile'";
        names[KeYParser.TRUE] = "'true'";
        names[KeYParser.FALSE] = "'false'";
        names[KeYParser.SAMEUPDATELEVEL] = "'\\sameUpdateLevel'";
        names[KeYParser.INSEQUENTSTATE] = "'\\inSequentState'";
        names[KeYParser.ANTECEDENTPOLARITY] = "'\\antecedentPolarity'";
        names[KeYParser.SUCCEDENTPOLARITY] = "'\\succedentPolarity'";
        names[KeYParser.CLOSEGOAL] = "'\\closegoal'";
        names[KeYParser.HEURISTICSDECL] = "'\\heuristicsDecl'";
        names[KeYParser.NONINTERACTIVE] = "'\\noninteractive'";
        names[KeYParser.DISPLAYNAME] = "'\\displayname'";
        names[KeYParser.HELPTEXT] = "'\\helptext'";
        names[KeYParser.REPLACEWITH] = "'\\replacewith'";
        names[KeYParser.ADDRULES] = "'\\addrules'";
        names[KeYParser.ADDPROGVARS] = "'\\addprogvars'";
        names[KeYParser.HEURISTICS] = "'\\heuristics'";
        names[KeYParser.FIND] = "'\\find'";
        names[KeYParser.ADD] = "'\\add'";
        names[KeYParser.ASSUMES] = "'\\assumes'";
        names[KeYParser.TRIGGER] = "'\\trigger'";
        names[KeYParser.AVOID] = "'\\avoid'";
        names[KeYParser.PREDICATES] = "'\\predicates'";
        names[KeYParser.FUNCTIONS] = "'\\functions'";
        names[KeYParser.TRANSFORMERS] = "'\\transformers'";
        names[KeYParser.UNIQUE] = "'\\unique'";
        names[KeYParser.RULES] = "'\\rules'";
        names[KeYParser.PROBLEM] = "'\\problem'";
        names[KeYParser.CHOOSECONTRACT] = "'\\chooseContract'";
        names[KeYParser.PROOFOBLIGATION] = "'\\proofObligation'";
        names[KeYParser.PROOF] = "'\\proof'";
        names[KeYParser.CONTRACTS] = "'\\contracts'";
        names[KeYParser.INVARIANTS] = "'\\invariants'";
        names[KeYParser.IN_TYPE] = "'\\inType'";
        names[KeYParser.IS_ABSTRACT_OR_INTERFACE] = "'\\isAbstractOrInterface'";
        names[KeYParser.CONTAINERTYPE] = "'\\containerType'";
        names[KeYParser.LIMITED] = "'$lmtd'";
        names[KeYParser.LOCSET] = "'\\locset'";
        names[KeYParser.SEQ] = "'\\seq'";
        names[KeYParser.BIGINT] = "'\\bigint'";
        names[KeYParser.UTF_PRECEDES] = "'\u227A'";
        names[KeYParser.UTF_IN] = "'\u220A'";
        names[KeYParser.UTF_EMPTY] = "'\u2205'";
        names[KeYParser.UTF_UNION] = "'\u222A'";
        names[KeYParser.UTF_INTERSECT] = "'\u2229'";
        names[KeYParser.UTF_SUBSET] = "'\u2286'";
        names[KeYParser.UTF_SETMINUS] = "'\u2216'";
        names[KeYParser.SEMI] = "';'";
        names[KeYParser.SLASH] = "'/'";
        names[KeYParser.BACKSLASH] = "'\\'";
        names[KeYParser.COLON] = "':'";
        names[KeYParser.DOUBLECOLON] = "'::'";
        names[KeYParser.ASSIGN] = "':='";
        names[KeYParser.DOT] = "'.'";
        names[KeYParser.COMMA] = "','";
        names[KeYParser.LPAREN] = "'('";
        names[KeYParser.RPAREN] = "')'";
        names[KeYParser.LBRACE] = "'{'";
        names[KeYParser.RBRACE] = "'}'";
        names[KeYParser.LBRACKET] = "'['";
        names[KeYParser.RBRACKET] = "']'";
        names[KeYParser.AT] = "'@'";
        names[KeYParser.EQUALS] = "'='";
        names[KeYParser.SEQARROW] = "'==>'";
        names[KeYParser.EXP] = "'^'";
        names[KeYParser.TILDE] = "'~'";
        names[KeYParser.PERCENT] = "'%'";
        names[KeYParser.STAR] = "'*'";
        names[KeYParser.MINUS] = "'-'";
        names[KeYParser.PLUS] = "'+'";
        names[KeYParser.GREATER] = "'>'";
        // ---- end generated token names ----
        tokenNames = names;
    }
}

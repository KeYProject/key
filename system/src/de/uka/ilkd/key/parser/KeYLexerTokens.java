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

    public synchronized static String[] getTokennames() {
        if(tokenNames == null) {
            prepareTokens();
        }
        return tokenNames;
    }

    static void prepareTokens() {
     // ---- begin generated token names ----
        tokenNames[KeYParser.SORTS] = "'\\sorts'";
        tokenNames[KeYParser.GENERIC] = "'\\generic'";
        tokenNames[KeYParser.PROXY] = "'\\proxy'";
        tokenNames[KeYParser.EXTENDS] = "'\\extends'";
        tokenNames[KeYParser.ONEOF] = "'\\oneof'";
        tokenNames[KeYParser.ABSTRACT] = "'\\abstract'";
        tokenNames[KeYParser.SCHEMAVARIABLES] = "'\\schemaVariables'";
        tokenNames[KeYParser.SCHEMAVAR] = "'\\schemaVar'";
        tokenNames[KeYParser.MODALOPERATOR] = "'\\modalOperator'";
        tokenNames[KeYParser.PROGRAM] = "'\\program'";
        tokenNames[KeYParser.FORMULA] = "'\\formula'";
        tokenNames[KeYParser.TERM] = "'\\term'";
        tokenNames[KeYParser.UPDATE] = "'\\update'";
        tokenNames[KeYParser.VARIABLES] = "'\\variables'";
        tokenNames[KeYParser.SKOLEMTERM] = "'\\skolemTerm'";
        tokenNames[KeYParser.SKOLEMFORMULA] = "'\\skolemFormula'";
        tokenNames[KeYParser.TERMLABEL] = "'\\termlabel'";
        tokenNames[KeYParser.MODIFIES] = "'\\modifies'";
        tokenNames[KeYParser.PROGRAMVARIABLES] = "'\\programVariables'";
        tokenNames[KeYParser.VARCOND] = "'\\varcond'";
        tokenNames[KeYParser.APPLY_UPDATE_ON_RIGID] = "'\\applyUpdateOnRigid'";
        tokenNames[KeYParser.DEPENDINGON] = "'\\dependingOn'";
        tokenNames[KeYParser.DISJOINTMODULONULL] = "'\\disjointModuloNull'";
        tokenNames[KeYParser.DROP_EFFECTLESS_ELEMENTARIES] = "'\\dropEffectlessElementaries'";
        tokenNames[KeYParser.DROP_EFFECTLESS_STORES] = "'\\dropEffectlessStores'";
        tokenNames[KeYParser.SIMPLIFY_IF_THEN_ELSE_UPDATE] = "'\\simplifyIfThenElseUpdate'";
        tokenNames[KeYParser.ENUM_CONST] = "'\\enumConstant'";
        tokenNames[KeYParser.FREELABELIN] = "'\\freeLabelIn'";
        tokenNames[KeYParser.HASSORT] = "'\\hasSort'";
        tokenNames[KeYParser.FIELDTYPE] = "'\\fieldType'";
        tokenNames[KeYParser.FINAL] = "'\\final'";
        tokenNames[KeYParser.ELEMSORT] = "'\\elemSort'";
        tokenNames[KeYParser.HASLABEL] = "'\\hasLabel'";
        tokenNames[KeYParser.HASSUBFORMULAS] = "'\\hasSubFormulas'";
        tokenNames[KeYParser.ISARRAY] = "'\\isArray'";
        tokenNames[KeYParser.ISARRAYLENGTH] = "'\\isArrayLength'";
        tokenNames[KeYParser.ISCONSTANT] = "'\\isConstant'";
        tokenNames[KeYParser.ISENUMTYPE] = "'\\isEnumType'";
        tokenNames[KeYParser.ISINDUCTVAR] = "'\\isInductVar'";
        tokenNames[KeYParser.ISLOCALVARIABLE] = "'\\isLocalVariable'";
        tokenNames[KeYParser.ISOBSERVER] = "'\\isObserver'";
        tokenNames[KeYParser.DIFFERENT] = "'\\different'";
        tokenNames[KeYParser.METADISJOINT] = "'\\metaDisjoint'";
        tokenNames[KeYParser.ISTHISREFERENCE] = "'\\isThisReference'";
        tokenNames[KeYParser.DIFFERENTFIELDS] = "'\\differentFields'";
        tokenNames[KeYParser.ISREFERENCE] = "'\\isReference'";
        tokenNames[KeYParser.ISREFERENCEARRAY] = "'\\isReferenceArray'";
        tokenNames[KeYParser.ISSTATICFIELD] = "'\\isStaticField'";
        tokenNames[KeYParser.ISSUBTYPE] = "'\\sub'";
        tokenNames[KeYParser.EQUAL_UNIQUE] = "'\\equalUnique'";
        tokenNames[KeYParser.NEW] = "'\\new'";
        tokenNames[KeYParser.NEWLABEL] = "'\\newLabel'";
        tokenNames[KeYParser.NOT_] = "'\\not'";
        tokenNames[KeYParser.NOTFREEIN] = "'\\notFreeIn'";
        tokenNames[KeYParser.SAME] = "'\\same'";
        tokenNames[KeYParser.STATIC] = "'\\static'";
        tokenNames[KeYParser.STATICMETHODREFERENCE] = "'\\staticMethodReference'";
        tokenNames[KeYParser.STRICT] = "'\\strict'";
        tokenNames[KeYParser.TYPEOF] = "'\\typeof'";
        tokenNames[KeYParser.INSTANTIATE_GENERIC] = "'\\instantiateGeneric'";
        tokenNames[KeYParser.SUBST] = "'\\subst'";
        tokenNames[KeYParser.IF] = "'\\if'";
        tokenNames[KeYParser.IFEX] = "'\\ifEx'";
        tokenNames[KeYParser.THEN] = "'\\then'";
        tokenNames[KeYParser.ELSE] = "'\\else'";
        tokenNames[KeYParser.INCLUDE] = "'\\include'";
        tokenNames[KeYParser.INCLUDELDTS] = "'\\includeLDTs'";
        tokenNames[KeYParser.CLASSPATH] = "'\\classpath'";
        tokenNames[KeYParser.BOOTCLASSPATH] = "'\\bootclasspath'";
        tokenNames[KeYParser.NODEFAULTCLASSES] = "'\\noDefaultClasses'";
        tokenNames[KeYParser.JAVASOURCE] = "'\\javaSource'";
        tokenNames[KeYParser.WITHOPTIONS] = "'\\withOptions'";
        tokenNames[KeYParser.OPTIONSDECL] = "'\\optionsDecl'";
        tokenNames[KeYParser.KEYSETTINGS] = "'\\settings'";
        tokenNames[KeYParser.PROFILE] = "'\\profile'";
        tokenNames[KeYParser.TRUE] = "'true'";
        tokenNames[KeYParser.FALSE] = "'false'";
        tokenNames[KeYParser.SAMEUPDATELEVEL] = "'\\sameUpdateLevel'";
        tokenNames[KeYParser.INSEQUENTSTATE] = "'\\inSequentState'";
        tokenNames[KeYParser.ANTECEDENTPOLARITY] = "'\\antecedentPolarity'";
        tokenNames[KeYParser.SUCCEDENTPOLARITY] = "'\\succedentPolarity'";
        tokenNames[KeYParser.CLOSEGOAL] = "'\\closegoal'";
        tokenNames[KeYParser.HEURISTICSDECL] = "'\\heuristicsDecl'";
        tokenNames[KeYParser.NONINTERACTIVE] = "'\\noninteractive'";
        tokenNames[KeYParser.DISPLAYNAME] = "'\\displayname'";
        tokenNames[KeYParser.HELPTEXT] = "'\\helptext'";
        tokenNames[KeYParser.REPLACEWITH] = "'\\replacewith'";
        tokenNames[KeYParser.ADDRULES] = "'\\addrules'";
        tokenNames[KeYParser.ADDPROGVARS] = "'\\addprogvars'";
        tokenNames[KeYParser.HEURISTICS] = "'\\heuristics'";
        tokenNames[KeYParser.FIND] = "'\\find'";
        tokenNames[KeYParser.ADD] = "'\\add'";
        tokenNames[KeYParser.ASSUMES] = "'\\assumes'";
        tokenNames[KeYParser.TRIGGER] = "'\\trigger'";
        tokenNames[KeYParser.AVOID] = "'\\avoid'";
        tokenNames[KeYParser.PREDICATES] = "'\\predicates'";
        tokenNames[KeYParser.FUNCTIONS] = "'\\functions'";
        tokenNames[KeYParser.TRANSFORMERS] = "'\\transformers'";
        tokenNames[KeYParser.UNIQUE] = "'\\unique'";
        tokenNames[KeYParser.RULES] = "'\\rules'";
        tokenNames[KeYParser.PROBLEM] = "'\\problem'";
        tokenNames[KeYParser.CHOOSECONTRACT] = "'\\chooseContract'";
        tokenNames[KeYParser.PROOFOBLIGATION] = "'\\proofObligation'";
        tokenNames[KeYParser.PROOF] = "'\\proof'";
        tokenNames[KeYParser.CONTRACTS] = "'\\contracts'";
        tokenNames[KeYParser.INVARIANTS] = "'\\invariants'";
        tokenNames[KeYParser.IN_TYPE] = "'\\inType'";
        tokenNames[KeYParser.IS_ABSTRACT_OR_INTERFACE] = "'\\isAbstractOrInterface'";
        tokenNames[KeYParser.CONTAINERTYPE] = "'\\containerType'";
        tokenNames[KeYParser.LIMITED] = "'$lmtd'";
        tokenNames[KeYParser.LOCSET] = "'\\locset'";
        tokenNames[KeYParser.SEQ] = "'\\seq'";
        tokenNames[KeYParser.BIGINT] = "'\\bigint'";
        tokenNames[KeYParser.UTF_PRECEDES] = "'\u227A'";
        tokenNames[KeYParser.UTF_IN] = "'\u220A'";
        tokenNames[KeYParser.UTF_EMPTY] = "'\u2205'";
        tokenNames[KeYParser.UTF_UNION] = "'\u222A'";
        tokenNames[KeYParser.UTF_INTERSECT] = "'\u2229'";
        tokenNames[KeYParser.UTF_SUBSET] = "'\u2286'";
        tokenNames[KeYParser.UTF_SETMINUS] = "'\u2216'";
        tokenNames[KeYParser.SEMI] = "';'";
        tokenNames[KeYParser.SLASH] = "'/'";
        tokenNames[KeYParser.BACKSLASH] = "'\\'";
        tokenNames[KeYParser.COLON] = "':'";
        tokenNames[KeYParser.DOUBLECOLON] = "'::'";
        tokenNames[KeYParser.ASSIGN] = "':='";
        tokenNames[KeYParser.DOT] = "'.'";
        tokenNames[KeYParser.COMMA] = "','";
        tokenNames[KeYParser.LPAREN] = "'('";
        tokenNames[KeYParser.RPAREN] = "')'";
        tokenNames[KeYParser.LBRACE] = "'{'";
        tokenNames[KeYParser.RBRACE] = "'}'";
        tokenNames[KeYParser.LBRACKET] = "'['";
        tokenNames[KeYParser.RBRACKET] = "']'";
        tokenNames[KeYParser.AT] = "'@'";
        tokenNames[KeYParser.EQUALS] = "'='";
        tokenNames[KeYParser.SEQARROW] = "'==>'";
        tokenNames[KeYParser.EXP] = "'^'";
        tokenNames[KeYParser.TILDE] = "'~'";
        tokenNames[KeYParser.PERCENT] = "'%'";
        tokenNames[KeYParser.STAR] = "'*'";
        tokenNames[KeYParser.MINUS] = "'-'";
        tokenNames[KeYParser.PLUS] = "'+'";
        tokenNames[KeYParser.GREATER] = "'>'";
        // ---- end generated token names ----
    }
}

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

package de.uka.ilkd.key.speclang.jml.pretranslation;

import de.uka.ilkd.key.parser.KeYLexerTokens;


/**
 * This class provides better literals to the tokens in the jml preparser.
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
 * created or using "KeYLexerTokensUpdater.g" which resides in package
 * {@code de.uka.ilkd.key.parser}.
 *
 * Proceed as follows (you may have to change paths of course)
 *
 * <pre>
 *   cp KeYLexerTokensUpdater.g $TMPDIR
 *   cp KeYJMLPreLexer.g $TMPDIR
 *   cp antlr-3.5.1.jar $TMPDIR
 *   cd $TMPDIR
 *   java -jar antlr-3.5.1.jar KeYLexerTokensUpdater.g
 *   javac -cp antlr-3.5.1.jar *.java
 *   java -cp antlr-3.5.1.jar:. KeYLexerTokensUpdaterParser "KeYJMLPreParser" < KeYJMLPreLexer.g
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
 * @see KeYLexerTokens
 */

public class KeYJMLPreLexerTokens {

    private KeYJMLPreLexerTokens() {
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
        String names[] = KeYJMLPreParser.tokenNames.clone();

        // ---- begin generated token names ----
        names[KeYJMLPreParser.ABSTRACT] = "'abstract'";
        names[KeYJMLPreParser.ACCESSIBLE] = "'accessible'";
        names[KeYJMLPreParser.ACCESSIBLE_REDUNDANTLY] = "'accessible_redundantly'";
        names[KeYJMLPreParser.ALSO] = "'also'";
        names[KeYJMLPreParser.ASSERT] = "'assert'";
        names[KeYJMLPreParser.ASSERT_REDUNDANTLY] = "'assert_redundantly'";
        names[KeYJMLPreParser.ASSUME] = "'assume'";
        names[KeYJMLPreParser.ASSUME_REDUNDANTLY] = "'assume_redundantly'";
        names[KeYJMLPreParser.ASSIGNABLE] = "'assignable'";
        names[KeYJMLPreParser.ASSIGNABLE_RED] = "'assignable_redundantly'";
        names[KeYJMLPreParser.AXIOM] = "'axiom'";
        names[KeYJMLPreParser.BEHAVIOR] = "'behavior'";
        names[KeYJMLPreParser.BEHAVIOUR] = "'behaviour'";
        names[KeYJMLPreParser.BREAKS] = "'breaks'";
        names[KeYJMLPreParser.BREAK_BEHAVIOR] = "'break_behavior'";
        names[KeYJMLPreParser.BREAK_BEHAVIOUR] = "'break_behaviour'";
        names[KeYJMLPreParser.CAPTURES] = "'captures'";
        names[KeYJMLPreParser.CAPTURES_RED] = "'captures_redundantly'";
        names[KeYJMLPreParser.CODE] = "'code'";
        names[KeYJMLPreParser.CODE_BIGINT_MATH] = "'code_bigint_math'";
        names[KeYJMLPreParser.CODE_JAVA_MATH] = "'code_java_math'";
        names[KeYJMLPreParser.CODE_SAFE_MATH] = "'code_safe_math'";
        names[KeYJMLPreParser.CONST] = "'const'";
        names[KeYJMLPreParser.CONSTRAINT] = "'constraint'";
        names[KeYJMLPreParser.CONSTRAINT_RED] = "'constraint_redundantly'";
        names[KeYJMLPreParser.CONTINUES] = "'continues'";
        names[KeYJMLPreParser.CONTINUE_BEHAVIOR] = "'continue_behavior'";
        names[KeYJMLPreParser.CONTINUE_BEHAVIOUR] = "'continue_behaviour'";
        names[KeYJMLPreParser.DEBUG] = "'debug'";
        names[KeYJMLPreParser.DECREASES] = "'decreases'";
        names[KeYJMLPreParser.DECREASES_REDUNDANTLY] = "'decreases_redundantly'";
        names[KeYJMLPreParser.DECREASING] = "'decreasing'";
        names[KeYJMLPreParser.DECREASING_REDUNDANTLY] = "'decreasing_redundantly'";
        names[KeYJMLPreParser.DETERMINES] = "'determines'";
        names[KeYJMLPreParser.DIVERGES] = "'diverges'";
        names[KeYJMLPreParser.DIVERGES_RED] = "'diverges_redundantly'";
        names[KeYJMLPreParser.DURATION] = "'duration'";
        names[KeYJMLPreParser.DURATION_RED] = "'duration_redundantly'";
        names[KeYJMLPreParser.ENSURES] = "'ensures'";
        names[KeYJMLPreParser.ENSURES_RED] = "'ensures_redundantly'";
        names[KeYJMLPreParser.EXCEPTIONAL_BEHAVIOR] = "'exceptional_behavior'";
        names[KeYJMLPreParser.EXCEPTIONAL_BEHAVIOUR] = "'exceptional_behaviour'";
        names[KeYJMLPreParser.EXSURES] = "'exsures'";
        names[KeYJMLPreParser.EXSURES_RED] = "'exsures_redundantly'";
        names[KeYJMLPreParser.FINAL] = "'final'";
        names[KeYJMLPreParser.FOR_EXAMPLE] = "'for_example'";
        names[KeYJMLPreParser.FORALL] = "'forall'";
        names[KeYJMLPreParser.GHOST] = "'ghost'";
        names[KeYJMLPreParser.HELPER] = "'helper'";
        names[KeYJMLPreParser.IMPLIES_THAT] = "'implies_that'";
        names[KeYJMLPreParser.IN] = "'in'";
        names[KeYJMLPreParser.IN_RED] = "'in_redundantly'";
        names[KeYJMLPreParser.INITIALLY] = "'initially'";
        names[KeYJMLPreParser.INSTANCE] = "'instance'";
        names[KeYJMLPreParser.INVARIANT] = "'invariant'";
        names[KeYJMLPreParser.INVARIANT_RED] = "'invariant_redundantly'";
        names[KeYJMLPreParser.LOOP_INVARIANT] = "'loop_invariant'";
        names[KeYJMLPreParser.LOOP_INVARIANT_RED] = "'loop_invariant_redundantly'";
        names[KeYJMLPreParser.MAINTAINING] = "'maintaining'";
        names[KeYJMLPreParser.MAINTAINING_REDUNDANTLY] = "'maintaining_redundantly'";
        names[KeYJMLPreParser.MAPS] = "'maps'";
        names[KeYJMLPreParser.MAPS_RED] = "'maps_redundantly'";
        names[KeYJMLPreParser.MEASURED_BY] = "'measured_by'";
        names[KeYJMLPreParser.MEASURED_BY_REDUNDANTLY] = "'measured_by_redundantly'";
        names[KeYJMLPreParser.MODEL] = "'model'";
        names[KeYJMLPreParser.MODEL_BEHAVIOR] = "'model_behavior'";
        names[KeYJMLPreParser.MODEL_BEHAVIOUR] = "'model_behaviour'";
        names[KeYJMLPreParser.MODIFIABLE] = "'modifiable'";
        names[KeYJMLPreParser.MODIFIABLE_RED] = "'modifiable_redundantly'";
        names[KeYJMLPreParser.MODIFIES] = "'modifies'";
        names[KeYJMLPreParser.MODIFIES_RED] = "'modifies_redundantly'";
        names[KeYJMLPreParser.MONITORED] = "'monitored'";
        names[KeYJMLPreParser.MONITORS_FOR] = "'monitors_for'";
        names[KeYJMLPreParser.NATIVE] = "'native'";
        names[KeYJMLPreParser.NON_NULL] = "'non_null'";
        names[KeYJMLPreParser.NORMAL_BEHAVIOR] = "'normal_behavior'";
        names[KeYJMLPreParser.NORMAL_BEHAVIOUR] = "'normal_behaviour'";
        names[KeYJMLPreParser.NO_STATE] = "'no_state'";
        names[KeYJMLPreParser.NOWARN] = "'nowarn'";
        names[KeYJMLPreParser.NULLABLE] = "'nullable'";
        names[KeYJMLPreParser.NULLABLE_BY_DEFAULT] = "'nullable_by_default'";
        names[KeYJMLPreParser.OLD] = "'old'";
        names[KeYJMLPreParser.POST] = "'post'";
        names[KeYJMLPreParser.POST_RED] = "'post_redundantly'";
        names[KeYJMLPreParser.PRE] = "'pre'";
        names[KeYJMLPreParser.PRE_RED] = "'pre_redundantly'";
        names[KeYJMLPreParser.PRIVATE] = "'private'";
        names[KeYJMLPreParser.PROTECTED] = "'protected'";
        names[KeYJMLPreParser.PUBLIC] = "'public'";
        names[KeYJMLPreParser.PURE] = "'pure'";
        names[KeYJMLPreParser.STRICTLY_PURE] = "'strictly_pure'";
        names[KeYJMLPreParser.READABLE] = "'readable'";
        names[KeYJMLPreParser.REPRESENTS] = "'represents'";
        names[KeYJMLPreParser.REPRESENTS_RED] = "'represents_redundantly'";
        names[KeYJMLPreParser.REQUIRES] = "'requires'";
        names[KeYJMLPreParser.REQUIRES_RED] = "'requires_redundantly'";
        names[KeYJMLPreParser.RETURNS] = "'returns'";
        names[KeYJMLPreParser.RETURN_BEHAVIOR] = "'return_behavior'";
        names[KeYJMLPreParser.RETURN_BEHAVIOUR] = "'return_behaviour'";
        names[KeYJMLPreParser.RESPECTS] = "'respects'";
        names[KeYJMLPreParser.SEPARATES] = "'separates'";
        names[KeYJMLPreParser.SET] = "'set'";
        names[KeYJMLPreParser.SIGNALS] = "'signals'";
        names[KeYJMLPreParser.SIGNALS_ONLY] = "'signals_only'";
        names[KeYJMLPreParser.SIGNALS_ONLY_RED] = "'signals_only_redundantly'";
        names[KeYJMLPreParser.SIGNALS_RED] = "'signals_redundantly'";
        names[KeYJMLPreParser.SPEC_BIGINT_MATH] = "'spec_bigint_math'";
        names[KeYJMLPreParser.SPEC_JAVA_MATH] = "'spec_java_math'";
        names[KeYJMLPreParser.SPEC_PROTECTED] = "'spec_protected'";
        names[KeYJMLPreParser.SPEC_PUBLIC] = "'spec_public'";
        names[KeYJMLPreParser.SPEC_NAME] = "'name'";
        names[KeYJMLPreParser.SPEC_SAFE_MATH] = "'spec_safe_math'";
        names[KeYJMLPreParser.STATIC] = "'static'";
        names[KeYJMLPreParser.STRICTFP] = "'strictfp'";
        names[KeYJMLPreParser.SYNCHRONIZED] = "'synchronized'";
        names[KeYJMLPreParser.TRANSIENT] = "'transient'";
        names[KeYJMLPreParser.TWO_STATE] = "'two_state'";
        names[KeYJMLPreParser.UNINITIALIZED] = "'uninitialized'";
        names[KeYJMLPreParser.UNREACHABLE] = "'unreachable'";
        names[KeYJMLPreParser.VOLATILE] = "'volatile'";
        names[KeYJMLPreParser.WHEN] = "'when'";
        names[KeYJMLPreParser.WHEN_RED] = "'when_redundantly'";
        names[KeYJMLPreParser.WORKING_SPACE] = "'working_space'";
        names[KeYJMLPreParser.WORKING_SPACE_RED] = "'working_space_redundantly'";
        names[KeYJMLPreParser.WRITABLE] = "'writable'";
        names[KeYJMLPreParser.SEMICOLON] = "';'";
        names[KeYJMLPreParser.AXIOM_NAME_BEGIN] = "'['";
        names[KeYJMLPreParser.AXIOM_NAME_END] = "']'";
        names[KeYJMLPreParser.LPAREN] = "'('";
        names[KeYJMLPreParser.RPAREN] = "')'";
        names[KeYJMLPreParser.EQUALITY] = "'='";
        names[KeYJMLPreParser.EMPTYBRACKETS] = "'[]'";
        names[KeYJMLPreParser.COMMA] = "','";
        names[KeYJMLPreParser.NEST_START] = "'{|'";
        names[KeYJMLPreParser.NEST_END] = "'|}'";
        // ---- end generated token names ----

        tokenNames = names;
    }
}

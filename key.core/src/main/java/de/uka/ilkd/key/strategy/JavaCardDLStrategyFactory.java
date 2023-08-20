/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.definition.AbstractStrategyPropertyDefinition;
import de.uka.ilkd.key.strategy.definition.OneOfStrategyPropertyDefinition;
import de.uka.ilkd.key.strategy.definition.StrategyPropertyValueDefinition;
import de.uka.ilkd.key.strategy.definition.StrategySettingsDefinition;
import de.uka.ilkd.key.strategy.feature.QueryExpandCost;

/**
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class JavaCardDLStrategyFactory implements StrategyFactory {

    /**
     * The unique {@link Name} of this {@link StrategyFactory}.
     */
    public static final Name NAME = new Name(JavaCardDLStrategy.JAVA_CARD_DL_STRATEGY);

    public static final String TOOL_TIP_STOP_AT_DEFAULT =
        "<html>Stop when (i) the maximum number of rule<br>"
            + "applications is reached or (ii) no more rules are<br>"
            + "applicable on the proof tree.</html>";
    public static final String TOOL_TIP_STOP_AT_UNCLOSABLE =
        "<html>Stop as soon as the first not automatically<br>"
            + "closable goal is encountered.</html>";
    public static final String TOOL_TIP_OSS_ON =
        "<html>" + "Turns on One Step Simplification. This will result in<br>"
            + "(sometimes significantly) shorter proofs which,<br>"
            + "however, are less transparent since simplification<br>"
            + "steps (rule applications) are combined in one OSS step." + "</html>";
    public static final String TOOL_TIP_OSS_OFF =
        "<html>" + "Turns off One Step Simplification. This will result in<br>"
            + "larger, but more transparent proof trees, since each<br>"
            + "simplification step is realized in one single rule<br>"
            + "application, with all instantiations clearly visible." + "</html>";
    public static final String TOOL_TIP_PROOF_SPLITTING_FREE =
        "<html>" + "Split formulas (if-then-else expressions,<br>"
            + "disjunctions in the antecedent, conjunctions in<br>"
            + "the succedent) freely without restrictions." + "</html>";
    public static final String TOOL_TIP_PROOF_SPLITTING_DELAYED =
        "<html>" + "Do not split formulas (if-then-else expressions,<br>"
            + "disjunctions in the antecedent, conjunctions in<br>"
            + "the succedent) as long as programs are present in<br>" + "the sequent.<br>"
            + "NB: This does not affect the splitting of formulas<br>"
            + "that themselves contain programs.<br>"
            + "NB2: Delaying splits often prevents KeY from finding<br>"
            + "short proofs, but in some cases it can significantly<br>"
            + "improve the performance." + "</html>";
    public static final String TOOL_TIP_PROOF_SPLITTING_OFF = "<html>"
        + "Do never split formulas (if-then-else expressions,<br>"
        + "disjunctions in the antecedent, conjunctions in<br>" + "the succedent).<br>"
        + "NB: This does not affect the splitting of formulas<br>" + "that contain programs.<br>"
        + "NB2: Without splitting, KeY is often unable to find<br>"
        + "proofs even for simple problems. This option can,<br>"
        + "nevertheless, be meaningful to keep the complexity<br>"
        + "of proofs small and support interactive proving." + "</html>";
    public static final String TOOL_TIP_LOOP_INVARIANT =
        "<html>" + "Use loop invariants for loops.<br>" + "Three properties have to be shown:<br>"
            + "<ul><li>Validity of invariant of a loop is preserved by the<br>"
            + "loop guard and loop body (initially valid).</li>"
            + "<li>If the invariant was valid at the start of the loop, it holds <br>"
            + "after arbitrarily many loop iterations (body preserves invariant).</li>"
            + "<li>Invariant holds after the loop terminates (use case).</li>" + "</ul></html>";
    public static final String TOOL_TIP_LOOP_SCOPE_INVARIANT = "<html>"
        + "Use loop (scope) invariants for loops.<br>" + "Three properties have to be shown:<br>"
        + "<ul><li>Validity of invariant of a loop is preserved by the<br>"
        + "loop guard and loop body (initially valid).</li>"
        + "<li>If the invariant was valid at the start of the loop, it holds <br>"
        + "after arbitrarily many loop iterations (body preserves invariant).</li>"
        + "<li>Invariant holds after the loop terminates (use case).</li>" + "</ul>"
        + "<p>In the loop scope invariant rule, the last two are combined "
        + "into a single goal.<br/>"
        + "This rule is easier to comprehend than the traditional rule in " + "the presence of<br/>"
        + "potentially exceptional program behavior.</p>" + "</html>";
    public static final String TOOL_TIP_LOOP_SCOPE_INVARIANT_TACLET =
        "<html>" + "Use the loop scope-based invariant taclet, i.e. not the built-in rules.<br>"
            + "Three properties have to be shown:<br>"
            + "<ul><li>Validity of invariant of a loop is preserved by the<br>"
            + "loop guard and loop body (initially valid).</li>"
            + "<li>If the invariant was valid at the start of the loop, it holds <br>"
            + "after arbitrarily many loop iterations (body preserves invariant).</li>"
            + "<li>Invariant holds after the loop terminates (use case).</li>" + "</ul>"
            + "<p>The last two are combined into a single goal or split into two<br>"
            + "goals based on the 'javaLoopTreatment' strategy option.</p>" + "</html>";
    public static final String TOOL_TIP_LOOP_SCOPE_EXPAND =
        "<html>" + "Unroll loop body, but with the loop scope technology.<br>"
            + "This requires less program transformation for irregular<br>"
            + "termination behavior." + "</html>";
    public static final String TOOL_TIP_LOOP_EXPAND = "<html>" + "Unroll loop body." + "</html>";
    public static final String TOOL_TIP_LOOP_NONE = "<html>" + "Leave loops untouched." + "</html>";
    public static final String TOOL_TIP_BLOCK_CONTRACT_INTERNAL = "<html>"
        + "Java blocks are replaced by their contracts.<br>" + "Three properties are shown:"
        + "<ul><li>Validity of block contract in the method context</li>"
        + "<li>Precondition of contract holds</li>"
        + "<li>Postcondition holds after block terminates</li>" + "</ul>" + "</html>";
    public static final String TOOL_TIP_BLOCK_CONTRACT_EXTERNAL =
        "<html>" + "Java blocks are replaced by their contracts.<br>" + "Two properties are shown:"
            + "<ul><li>Precondition of contract holds</li>"
            + "<li>Postcondition holds after block terminates</li>" + "</ul></html>";
    public static final String TOOL_TIP_BLOCK_EXPAND =
        "<html>" + "Do not use block contracts for Java blocks. Expand Java blocks." + "</html>";
    public static final String TOOL_TIP_METHOD_CONTRACT =
        "<html>Replace method calls by contracts. In some cases<br>"
            + "a method call may also be replaced by its method body.<br>"
            + "If query treatment is activated, this behavior applies<br>"
            + "to queries as well.</html>";
    public static final String TOOL_TIP_METHOD_EXPAND =
        "<html>Replace method calls by their bodies, i.e. by their<br>"
            + "implementation. Method contracts are strictly deactivated.</html>";
    public static final String TOOL_TIP_METHOD_NONE =
        "<html>" + "Stop when encountering a method" + "</html>";
    public static final String TOOL_TIP_MPS_MERGE =
        "<html>Use merge point statements for merging. That is,<br>"
            + "whenever all branches with a given merge point statement<br>"
            + "have reached it, the strategies will eventually merge<br>"
            + "the branches together using the merge point specification.</html>";
    public static final String TOOL_TIP_MPS_SKIP =
        "<html>Simply removes (skips) the merge point statment;<br>"
            + "no state merging is applied.</html>";
    public static final String TOOL_TIP_MPS_NONE =
        "<html>" + "Stop when encountering a merge point statement" + "</html>";
    public static final String TOOL_TIP_CLASSAXIOM_FREE =
        "<html>Expand class axioms (such as invariants) freely.</html>";
    public static final String TOOL_TIP_CLASSAXIOM_DELAYED =
        "<html>Expand class axioms (such as invariants) only after " + "symbolic execution.</html>";
    public static final String TOOL_TIP_CLASSAXIOM_OFF =
        "<html>Do not expand class axioms (such as invariants).</html>";
    public static final String TOOL_TIP_DEPENDENCY_ON =
        "<html>Uses the information in JML's <tt>accessible</tt> clauses<br>"
            + "in order to simplify heap terms. For instance, consider the term<br>"
            + "<center><i>f(store(heap,o,a,1))</i></center>"
            + "If <i>f</i> does not depend on the location <i>(o,a)</i>, which is<br>"
            + "expressed by an <tt>accessible</tt> clause, then the term can be <br>"
            + "simplified to <i>f(heap)</i>.</html>";
    public static final String TOOL_TIP_DEPENDENCY_OFF =
        "<html>Does <i>not</i> use the framing information contained in JML's <br>"
            + "<tt>accessible</tt> clauses automatically in order to simplify heap terms.<br>"
            + "This prevents the automatic proof search to find proofs for a "
            + "number of problems.<br>"
            + "On the other hand, the automatic proof search does not use a particular order in<br>"
            + "which <tt>accessible</tt> clauses are used. Since the usage of "
            + "an <tt>accessible</tt><br>"
            + "clause is splitting, this might result in huge (or even infeasible) proofs.</html>";
    public static final String TOOL_TIP_QUERY_ON =
        "<html>Rewrite query to a method call so that contracts or inlining<br>"
            + "can be used. A query is a method that is used as a function <br>"
            + "in the logic and stems from the specification.<br><br>"
            + "Whether contracts or inlining are used depends on the <br>"
            + "Method Treatment settings.</html>";
    public static final String TOOL_TIP_QUERY_RESTRICTED =
        "<html>Rewrite query to a method call (expanded) so that "
            + "contracts or inlining can be used.<br>"
            + "<ul><li> Priority of expanding queries occuring earlier on a "
            + "branch is higher than<br>"
            + " for queries introduced more recently. This approximates in a "
            + "breath-first search<br>" + " with respect to query expansion.</li>"
            + "<li> Reexpansion of identical query terms is suppressed.</li>"
            + "<li> A query is not expanded if one of its arguments contains a literal greater<br>"
            + " than " + QueryExpandCost.CONSIDERED_AS_BIG_LITERAL + ", or smaller than "
            + (-QueryExpandCost.CONSIDERED_AS_BIG_LITERAL)
            + ". This helps detecting loops in a proof.</li>"
            + "<li> Queries are expanded after the loop body in the \"Preserves Invariant\"<br>"
            + " branch of the loop invariant rule.</li>"
            + "<li> Queries are expanded in the Base Case and the conclusio of the Step Case <br>"
            + " branch when using Auto Induction.</li>" + "</ul></html>";
    public static final String TOOL_TIP_QUERY_OFF =
        "<html>" + "Turn rewriting of query off." + "</html>";
    public static final String TOOL_TIP_EXPAND_LOCAL_QUERIES_ON =
        "<html>Replaces queries by their method body in certain safe cases.<br>" + "Safe cases are:"
            + "<ul><li>the return type of the expanded method is known</li>"
            + "<li>the object on which the methodcall is invoked, is self or "
            + "a parent of self</li></ul>"
            + "This mechanism works independently of the query treatment <br>"
            + "and method treatment settings above.<br>"
            + "<i>The internal rule name is Query Axiom</i></html>";
    public static final String TOOL_TIP_EXPAND_LOCAL_QUERIES_OFF =
        "<html>" + "Expansion of local queries is turned off. <br>"
            + "This setting is independent of the query treatment setting." + "</html>";
    public static final String TOOL_TIP_ARITHMETIC_BASE = "<html>" + "Basic arithmetic support:"
        + "<ul>" + "<li>Simplification of polynomial expressions</li>"
        + "<li>Computation of Gr&ouml;bner Bases for polynomials in the antecedent</li>"
        + "<li>(Partial) Omega procedure for handling linear inequations</li>" + "</ul>"
        + "</html>";
    public static final String TOOL_TIP_ARITHMETIC_DEF_OPS =
        "<html>" + "Automatically expand defined symbols like:" + "<ul>"
            + "<li><tt>/</tt>, <tt>%</tt>, <tt>jdiv</tt>, <tt>jmod</tt>, ...</li>"
            + "<li><tt>int_RANGE</tt>, <tt>short_MIN</tt>, ...</li>"
            + "<li><tt>inInt</tt>, <tt>inByte</tt>, ...</li>"
            + "<li><tt>addJint</tt>, <tt>mulJshort</tt>, ...</li>" + "</ul>" + "</html>";
    public static final String TOOL_TIP_ARITHMETIC_MODEL_SEARCH = "<html>"
        + "Support for non-linear inequations and model search.<br>" + "In addition, this performs:"
        + "<ul>" + "<li>Multiplication of inequations with each other</li>"
        + "<li>Systematic case distinctions (cuts)</li>" + "</ul>"
        + "This method is guaranteed to find counterexamples for<br>"
        + "invalid goals that only contain polynomial (in)equations.<br>"
        + "Such counterexamples turn up as trivially unprovable goals.<br>"
        + "It is also able to prove many more valid goals involving<br>"
        + "(in)equations, but will in general not terminate on such goals." + "</html>";
    public static final String TOOL_TIP_QUANTIFIER_NONE =
        "<html>" + "Do not instantiate quantified formulas automatically" + "</html>";
    public static final String TOOL_TIP_QUANTIFIER_NO_SPLITS = "<html>"
        + "Instantiate quantified formulas automatically<br>"
        + "with terms that occur in a sequent, but only if<br>"
        + "this does not cause proof splitting. Further, quantified<br>"
        + "formulas that contain queries are not instantiated<br>" + "automatically." + "</html>";
    public static final String TOOL_TIP_QUANTIFIER_NO_SPLITS_WITH_PROGS =
        "<html>" + "Instantiate quantified formulas automatically<br>"
            + "with terms that occur in a sequent, but if the<br>"
            + "sequent contains programs then only perform<br>"
            + "instantiations that do not cause proof splitting.<br>"
            + "Further, quantified formulas that contain queries<br>"
            + "are not instantiated automatically." + "</html>";
    public static final String TOOL_TIP_QUANTIFIER_FREE =
        "<html>" + "Instantiate quantified formulas automatically<br>"
            + "with terms that occur in a sequent, also if this<br>"
            + "might cause proof splitting." + "</html>";
    public static final String TOOL_TIP_AUTO_INDUCTION_ON =
        "<html>" + "Create an inductive proof for formulas of the form:<br>"
            + "      ==>  \\forall int i; 0&lt;=i->phi <br>"
            + "and certain other forms. The induction hypothesis<br>"
            + "is the subformula phi. The rule is applied before<br>"
            + "beta rules are applied.<br>" + "<br>" + "When encountering a formula of the form<br>"
            + "      ==>  (\\forall int i; 0&lt;=i->phi) & psi <br>"
            + "and certain similar forms, then the quantified formula<br>"
            + "is used in the Use Case branch as a lemma for psi,<br>"
            + "i.e., the sequent in the Use Case has the form:<br>"
            + "      (\\forall int i; 0&lt;=i->phi) ==>  psi <br>" + "</html>";
    public static final String TOOL_TIP_AUTO_INDUCTION_RESTRICTED =
        "<html>" + "Performs auto induction only on quantified formulas that<br>"
            + "(a) fullfill a certain pattern (as described for the \"on\"option)<br>"
            + "and (b) whose quantified variable has the suffix \"Ind\" or \"IND\".<br>"
            + "For instance, auto induction will be applied on:<br>"
            + "      ==>  \\forall int iIND; 0&lt;=iIND->phi <br>" + "but not on: <br>"
            + "      ==>  \\forall int i; 0&lt;=i->phi <br>" + "</html>";
    public static final String TOOL_TIP_AUTO_INDUCTION_OFF =
        "<html>" + "Deactivates automatic creation of inductive proofs.<br>"
            + "In order to make use of auto induction, activate <br>"
            + "auto induction early in proofs before the <br>"
            + "quantified formula that is to be proven inductively<br>"
            + "is Skolemized (using the delta rule). Auto induction<br>"
            + "is not applied on Skolemized formulas in order to<br>"
            + "limit the number of inductive proofs." + "</html>";

    public JavaCardDLStrategyFactory() {
    }

    public static final String toolTipUserOff(int i) {
        return "Taclets of the rule set \"userTaclets" + i + "\" are not applied automatically";
    }

    public static final String toolTipUserLow(int i) {
        return "Taclets of the rule set \"userTaclets" + i
            + "\" are applied automatically with low priority";
    }

    public static final String toolTipUserHigh(int i) {
        return "Taclets of the rule set \"userTaclets" + i
            + "\" are applied automatically with high priority";
    }

    private static OneOfStrategyPropertyDefinition getStopAt() {
        return new OneOfStrategyPropertyDefinition(StrategyProperties.STOPMODE_OPTIONS_KEY,
            "Stop at",
            new StrategyPropertyValueDefinition(StrategyProperties.STOPMODE_DEFAULT, "Default",
                TOOL_TIP_STOP_AT_DEFAULT),
            new StrategyPropertyValueDefinition(StrategyProperties.STOPMODE_NONCLOSE, "Unclosable",
                TOOL_TIP_STOP_AT_UNCLOSABLE));
    }

    private static OneOfStrategyPropertyDefinition getOssUsage() {
        return new OneOfStrategyPropertyDefinition(StrategyProperties.OSS_OPTIONS_KEY,
            "One Step Simplification",
            new StrategyPropertyValueDefinition(StrategyProperties.OSS_ON, "Enabled",
                TOOL_TIP_OSS_ON),
            new StrategyPropertyValueDefinition(StrategyProperties.OSS_OFF, "Disabled",
                TOOL_TIP_OSS_OFF));
    }

    private static OneOfStrategyPropertyDefinition getProofSplitting() {
        return new OneOfStrategyPropertyDefinition(StrategyProperties.SPLITTING_OPTIONS_KEY,
            "Proof splitting",
            new StrategyPropertyValueDefinition(StrategyProperties.SPLITTING_NORMAL, "Free",
                TOOL_TIP_PROOF_SPLITTING_FREE),
            new StrategyPropertyValueDefinition(StrategyProperties.SPLITTING_DELAYED, "Delayed",
                TOOL_TIP_PROOF_SPLITTING_DELAYED),
            new StrategyPropertyValueDefinition(StrategyProperties.SPLITTING_OFF, "Off",
                TOOL_TIP_PROOF_SPLITTING_OFF));
    }

    private static OneOfStrategyPropertyDefinition getLoopTreatment() {
        return new OneOfStrategyPropertyDefinition(StrategyProperties.LOOP_OPTIONS_KEY,
            "Loop treatment", 2,
            /*
             * NOTE (DS, 2019-04-10): Deactivated the built-in loop scope rule since we now have the
             * loop scope taclets which are based on the same theory, but offer several advantages.
             */
            // new StrategyPropertyValueDefinition(
            // StrategyProperties.LOOP_SCOPE_INVARIANT,
            // "Loop Scope Invariant", TOOL_TIP_LOOP_SCOPE_INVARIANT),
            new StrategyPropertyValueDefinition(StrategyProperties.LOOP_SCOPE_INV_TACLET,
                "Invariant (Loop Scope)", TOOL_TIP_LOOP_SCOPE_INVARIANT_TACLET),
            new StrategyPropertyValueDefinition(StrategyProperties.LOOP_SCOPE_EXPAND,
                "Expand (Loop Scope)", TOOL_TIP_LOOP_SCOPE_EXPAND),
            new StrategyPropertyValueDefinition(StrategyProperties.LOOP_INVARIANT,
                "Invariant (Transformation)", TOOL_TIP_LOOP_INVARIANT),
            new StrategyPropertyValueDefinition(StrategyProperties.LOOP_EXPAND,
                "Expand (Transformation)", TOOL_TIP_LOOP_EXPAND),
            new StrategyPropertyValueDefinition(StrategyProperties.LOOP_NONE, "None",
                TOOL_TIP_LOOP_NONE));
    }

    private static OneOfStrategyPropertyDefinition getBlockTreatment() {
        return new OneOfStrategyPropertyDefinition(StrategyProperties.BLOCK_OPTIONS_KEY,
            "Block treatment", 1,
            new StrategyPropertyValueDefinition(StrategyProperties.BLOCK_CONTRACT_INTERNAL,
                "Internal Contract", TOOL_TIP_BLOCK_CONTRACT_INTERNAL),
            new StrategyPropertyValueDefinition(StrategyProperties.BLOCK_CONTRACT_EXTERNAL,
                "External Contract", TOOL_TIP_BLOCK_CONTRACT_EXTERNAL),
            new StrategyPropertyValueDefinition(StrategyProperties.BLOCK_EXPAND, "Expand",
                TOOL_TIP_BLOCK_EXPAND));
    }

    private static OneOfStrategyPropertyDefinition getMethodTreatment() {
        return new OneOfStrategyPropertyDefinition(StrategyProperties.METHOD_OPTIONS_KEY,
            "Method treatment",
            new StrategyPropertyValueDefinition(StrategyProperties.METHOD_CONTRACT, "Contract",
                TOOL_TIP_METHOD_CONTRACT),
            new StrategyPropertyValueDefinition(StrategyProperties.METHOD_EXPAND, "Expand",
                TOOL_TIP_METHOD_EXPAND),
            new StrategyPropertyValueDefinition(StrategyProperties.METHOD_NONE, "None",
                TOOL_TIP_METHOD_NONE));
    }

    private static OneOfStrategyPropertyDefinition getMergePointStatementTreatment() {
        return new OneOfStrategyPropertyDefinition(StrategyProperties.MPS_OPTIONS_KEY,
            "Merge point statements",
            new StrategyPropertyValueDefinition(StrategyProperties.MPS_MERGE, "Merge",
                TOOL_TIP_MPS_MERGE),
            new StrategyPropertyValueDefinition(StrategyProperties.MPS_SKIP, "Skip",
                TOOL_TIP_MPS_SKIP),
            new StrategyPropertyValueDefinition(StrategyProperties.MPS_NONE, "None",
                TOOL_TIP_MPS_NONE));
    }

    private static OneOfStrategyPropertyDefinition getDependencyContracts() {
        return new OneOfStrategyPropertyDefinition(StrategyProperties.DEP_OPTIONS_KEY,
            "Dependency contracts",
            new StrategyPropertyValueDefinition(StrategyProperties.DEP_ON, "On",
                TOOL_TIP_DEPENDENCY_ON),
            new StrategyPropertyValueDefinition(StrategyProperties.DEP_OFF, "Off",
                TOOL_TIP_DEPENDENCY_OFF));
    }

    private static OneOfStrategyPropertyDefinition getQueryTreatment() {
        final OneOfStrategyPropertyDefinition expandLocalQueries =
            new OneOfStrategyPropertyDefinition(StrategyProperties.QUERYAXIOM_OPTIONS_KEY,
                "Expand local queries:",
                new StrategyPropertyValueDefinition(StrategyProperties.QUERYAXIOM_ON, "On",
                    TOOL_TIP_EXPAND_LOCAL_QUERIES_ON),
                new StrategyPropertyValueDefinition(StrategyProperties.QUERYAXIOM_OFF, "Off",
                    TOOL_TIP_EXPAND_LOCAL_QUERIES_OFF));
        return new OneOfStrategyPropertyDefinition(StrategyProperties.QUERY_OPTIONS_KEY,
            "Query treatment", new AbstractStrategyPropertyDefinition[] { expandLocalQueries },
            new StrategyPropertyValueDefinition(StrategyProperties.QUERY_ON, "On",
                TOOL_TIP_QUERY_ON),
            new StrategyPropertyValueDefinition(StrategyProperties.QUERY_RESTRICTED, "Restricted",
                TOOL_TIP_QUERY_RESTRICTED),
            new StrategyPropertyValueDefinition(StrategyProperties.QUERY_OFF, "Off",
                TOOL_TIP_QUERY_OFF));
    }

    private static OneOfStrategyPropertyDefinition getArithmeticTreatment() {
        return new OneOfStrategyPropertyDefinition(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY,
            "Arithmetic treatment",
            new StrategyPropertyValueDefinition(StrategyProperties.NON_LIN_ARITH_NONE, "Basic",
                TOOL_TIP_ARITHMETIC_BASE),
            new StrategyPropertyValueDefinition(StrategyProperties.NON_LIN_ARITH_DEF_OPS, "DefOps",
                TOOL_TIP_ARITHMETIC_DEF_OPS),
            new StrategyPropertyValueDefinition(StrategyProperties.NON_LIN_ARITH_COMPLETION,
                "Model Search", TOOL_TIP_ARITHMETIC_MODEL_SEARCH));
    }

    private static OneOfStrategyPropertyDefinition getQuantifierTreatment() {
        return new OneOfStrategyPropertyDefinition(StrategyProperties.QUANTIFIERS_OPTIONS_KEY,
            "Quantifier treatment", 2,
            new StrategyPropertyValueDefinition(StrategyProperties.QUANTIFIERS_NONE, "None",
                TOOL_TIP_QUANTIFIER_NONE, 2, 4),
            new StrategyPropertyValueDefinition(StrategyProperties.QUANTIFIERS_NON_SPLITTING,
                "No Splits", TOOL_TIP_QUANTIFIER_NO_SPLITS, 6, 2),
            new StrategyPropertyValueDefinition(
                StrategyProperties.QUANTIFIERS_NON_SPLITTING_WITH_PROGS, "No Splits with Progs",
                TOOL_TIP_QUANTIFIER_NO_SPLITS_WITH_PROGS, 2, 4),
            new StrategyPropertyValueDefinition(StrategyProperties.QUANTIFIERS_INSTANTIATE, "Free",
                TOOL_TIP_QUANTIFIER_FREE, 6, 2));
    }

    private static OneOfStrategyPropertyDefinition getClassAxiom() {
        return new OneOfStrategyPropertyDefinition(StrategyProperties.CLASS_AXIOM_OPTIONS_KEY,
            "Class axiom rule",
            new StrategyPropertyValueDefinition(StrategyProperties.CLASS_AXIOM_FREE, "Free",
                TOOL_TIP_CLASSAXIOM_FREE),
            new StrategyPropertyValueDefinition(StrategyProperties.CLASS_AXIOM_DELAYED, "Delayed",
                TOOL_TIP_CLASSAXIOM_DELAYED),
            new StrategyPropertyValueDefinition(StrategyProperties.CLASS_AXIOM_OFF, "Off",
                TOOL_TIP_CLASSAXIOM_OFF));
    }

    private static OneOfStrategyPropertyDefinition getAutoInduction() {
        return new OneOfStrategyPropertyDefinition(StrategyProperties.AUTO_INDUCTION_OPTIONS_KEY,
            "Auto Induction",
            new StrategyPropertyValueDefinition(StrategyProperties.AUTO_INDUCTION_LEMMA_ON, "On",
                TOOL_TIP_AUTO_INDUCTION_ON),
            new StrategyPropertyValueDefinition(StrategyProperties.AUTO_INDUCTION_RESTRICTED,
                "Restricted", TOOL_TIP_AUTO_INDUCTION_RESTRICTED),
            new StrategyPropertyValueDefinition(StrategyProperties.AUTO_INDUCTION_OFF, "Off",
                TOOL_TIP_AUTO_INDUCTION_OFF));
    }

    private static OneOfStrategyPropertyDefinition getUserOptions() {
        // User properties
        List<AbstractStrategyPropertyDefinition> props = new LinkedList<>();
        for (int i = 1; i <= StrategyProperties.USER_TACLETS_NUM; ++i) {
            OneOfStrategyPropertyDefinition user = new OneOfStrategyPropertyDefinition(
                StrategyProperties.userTacletsOptionsKey(i), i + ":  ",
                new StrategyPropertyValueDefinition(StrategyProperties.USER_TACLETS_OFF, "Off",
                    toolTipUserOff(i), 3, 1),
                new StrategyPropertyValueDefinition(StrategyProperties.USER_TACLETS_LOW,
                    "Low prior.", toolTipUserLow(i), 4, 2),
                new StrategyPropertyValueDefinition(StrategyProperties.USER_TACLETS_HIGH,
                    "High prior.", toolTipUserHigh(i), 6, 2));
            props.add(user);
        }

        return new OneOfStrategyPropertyDefinition(null, "User-specific taclet sets",
            "<html>" + "These options define whether user- and problem-specific taclet sets<br>"
                + "are applied automatically by the strategy. Problem-specific taclets<br>"
                + "can be defined in the \\rules-section of a .key-problem file. For<br>"
                + "automatic application, the taclets have to contain a clause<br>"
                + "\\heuristics(userTaclets1), \\heuristics(userTaclets2), etc." + "</html>",
            -1, props.toArray(new AbstractStrategyPropertyDefinition[0]));
    }

    public Strategy create(Proof proof, StrategyProperties strategyProperties) {
        return new JavaCardDLStrategy(proof, strategyProperties);
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public StrategySettingsDefinition getSettingsDefinition() {
        // Properties
        final OneOfStrategyPropertyDefinition stopAt = getStopAt();
        final OneOfStrategyPropertyDefinition ossUsage = getOssUsage();
        final OneOfStrategyPropertyDefinition proofSplitting = getProofSplitting();
        final OneOfStrategyPropertyDefinition loopTreatment = getLoopTreatment();
        final OneOfStrategyPropertyDefinition blockTreatment = getBlockTreatment();
        final OneOfStrategyPropertyDefinition methodTreatment = getMethodTreatment();
        final OneOfStrategyPropertyDefinition mergePointStatementTreatment =
            getMergePointStatementTreatment();
        final OneOfStrategyPropertyDefinition dependencyContracts = getDependencyContracts();
        final OneOfStrategyPropertyDefinition queryTreatment = getQueryTreatment();
        final OneOfStrategyPropertyDefinition arithmeticTreatment = getArithmeticTreatment();
        final OneOfStrategyPropertyDefinition quantifierTreatment = getQuantifierTreatment();
        final OneOfStrategyPropertyDefinition classAxiom = getClassAxiom();
        final OneOfStrategyPropertyDefinition autoInduction = getAutoInduction();
        final OneOfStrategyPropertyDefinition userOptions = getUserOptions();
        // Model
        return new StrategySettingsDefinition("Java DL Options", stopAt, ossUsage, proofSplitting,
            loopTreatment, blockTreatment, methodTreatment, mergePointStatementTreatment,
            dependencyContracts, queryTreatment, arithmeticTreatment, quantifierTreatment,
            classAxiom, autoInduction, userOptions);
    }
}

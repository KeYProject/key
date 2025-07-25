/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;


import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.definition.AbstractStrategyPropertyDefinition;
import de.uka.ilkd.key.strategy.definition.OneOfStrategyPropertyDefinition;
import de.uka.ilkd.key.strategy.definition.StrategyPropertyValueDefinition;
import de.uka.ilkd.key.strategy.definition.StrategySettingsDefinition;
import de.uka.ilkd.key.strategy.feature.QueryExpandCost;

import org.key_project.logic.Name;


/**
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class JavaCardDLStrategyFactory implements StrategyFactory {

    /**
     * The unique {@link Name} of this {@link StrategyFactory}.
     */
    public static final Name NAME = new Name(JavaCardDLStrategy.JAVA_CARD_DL_STRATEGY);

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

    @Override
    public JavaCardDLStrategy create(Proof proof, StrategyProperties strategyProperties) {
        return new JavaCardDLStrategy(proof, strategyProperties);
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public StrategySettingsDefinition getSettingsDefinition() {
        // Properties
        final OneOfStrategyPropertyDefinition ossUsage = getOssUsage();
        final OneOfStrategyPropertyDefinition proofSplitting = getProofSplitting();
        final OneOfStrategyPropertyDefinition dependencyContracts = getDependencyContracts();
        final OneOfStrategyPropertyDefinition queryTreatment = getQueryTreatment();
        final OneOfStrategyPropertyDefinition quantifierTreatment = getQuantifierTreatment();
        final OneOfStrategyPropertyDefinition classAxiom = getClassAxiom();
        final OneOfStrategyPropertyDefinition autoInduction = getAutoInduction();
        // Model
        return new StrategySettingsDefinition("Java DL Options", ossUsage, proofSplitting,
            dependencyContracts, queryTreatment, quantifierTreatment,
            classAxiom, autoInduction);
    }
}

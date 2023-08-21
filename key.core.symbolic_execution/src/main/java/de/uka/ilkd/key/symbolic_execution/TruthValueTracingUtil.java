/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution;

import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.FormulaTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.IfFormulaInstSeq;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.OneStepSimplifierRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.util.NodePreorderIterator;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.java.ArrayUtil;

/**
 * Provides functionality to evaluate the truth value of labeled formulas (predicates and junctors).
 *
 * @author Martin Hentschel
 */
public final class TruthValueTracingUtil {
    /**
     * Forbid instances.
     */
    private TruthValueTracingUtil() {
    }

    /**
     * Checks if the given {@link SequentFormula} is a predicate.
     *
     * @param sequentFormula The {@link SequentFormula} to check.
     * @return {@code true} is predicate, {@code false} is something else.
     */
    public static boolean isPredicate(SequentFormula sequentFormula) {
        return sequentFormula != null && isPredicate(sequentFormula.formula());
    }

    /**
     * Checks if the given {@link Term} is a predicate.
     *
     * @param term The {@link Term} to check.
     * @return {@code true} is predicate, {@code false} is something else.
     */
    public static boolean isPredicate(Term term) {
        return term != null && isPredicate(term.op());
    }

    /**
     * Checks if the given {@link Operator} is a predicate.
     *
     * @param operator The {@link Operator} to check.
     * @return {@code true} is predicate, {@code false} is something else.
     */
    public static boolean isPredicate(Operator operator) {
        if (operator == Equality.EQV) {
            return false;
        } else if (operator instanceof Junctor) {
            return operator == Junctor.TRUE || operator == Junctor.FALSE;
        } else if (operator == AbstractTermTransformer.META_EQ
                || operator == AbstractTermTransformer.META_GEQ
                || operator == AbstractTermTransformer.META_GREATER
                || operator == AbstractTermTransformer.META_LEQ
                || operator == AbstractTermTransformer.META_LESS) {
            return true; // These Meta constructs evaluate always to true or false
        } else if (operator instanceof SortedOperator) {
            return ((SortedOperator) operator).sort() == Sort.FORMULA;
        } else {
            return false;
        }
    }

    /**
     * Checks if the given {@link Term} is a logical operator
     *
     * @param operator The {@link Term} to check.
     * @return {@code true} is logical operator, {@code false} is something else.
     */
    public static boolean isLogicOperator(Term term) {
        if (term != null) {
            return isLogicOperator(term.op(), term.subs());
        } else {
            return false;
        }
    }

    /**
     * Checks if the given {@link Operator} and its sub {@link Term}s specify a logical operator.
     *
     * @param operator The {@link Operator}.
     * @param subs The sub {@link Term}s.
     * @return {@code true} is logical operator, {@code false} is something else.
     */
    public static boolean isLogicOperator(Operator operator, ImmutableArray<Term> subs) {
        if (operator instanceof Junctor) {
            return operator != Junctor.TRUE && operator != Junctor.FALSE;
        } else if (operator == Equality.EQV) {
            return true;
        } else
            return isIfThenElseFormula(operator, subs);
    }

    /**
     * Checks if the given {@link Term} is an if-then-else formula.
     *
     * @param term The {@link Term} to check.
     * @return {@code true} is if-then-else formula, {@code false} is something else.
     */
    public static boolean isIfThenElseFormula(Term term) {
        if (term != null) {
            return isIfThenElseFormula(term.op(), term.subs());
        } else {
            return false;
        }
    }

    /**
     * Checks if the given {@link Operator} and its sub {@link Term}s specify an if-then-else
     * formula.
     *
     * @param operator The {@link Operator}.
     * @param subs The sub {@link Term}s.
     * @return {@code true} is if-then-else formula, {@code false} is something else.
     */
    public static boolean isIfThenElseFormula(Operator operator, ImmutableArray<Term> subs) {
        if (operator == IfThenElse.IF_THEN_ELSE) {
            Sort sort = operator.sort(subs);
            return sort == Sort.FORMULA;
        } else {
            return false;
        }
    }

    /**
     * Evaluates the truth values in the subtree of the given {@link Node} for predicates labeled
     * with the given {@link TermLabel} name.
     *
     * @param node The {@link Node} to start evaluation at.
     * @param termLabelName The {@link Name} of the {@link TermLabel} to consider.
     * @param useUnicode {@code true} use unicode characters, {@code false} do not use unicode
     *        characters.
     * @param usePrettyPrinting {@code true} use pretty printing, {@code false} do not use pretty
     *        printing.
     * @return The result.
     * @throws ProofInputException Occurred Exception
     */
    public static TruthValueTracingResult evaluate(Node node, Name termLabelName,
            boolean useUnicode, boolean usePrettyPrinting) throws ProofInputException {
        TruthValueTracingResult result = new TruthValueTracingResult();
        Deque<Map<String, MultiEvaluationResult>> evaluationStack =
            new LinkedList<>();
        evaluationStack.addFirst(new HashMap<>());
        Services services = node.proof().getServices();
        NodePreorderIterator iterator = new NodePreorderIterator(node);
        while (iterator.hasNext()) {
            // Get next node
            int childIndexOnParnt = iterator.getChildIndexOnParent(); // Needs to be called before
                                                                      // next is called.
            Node next = iterator.next();
            // Create child result for current node
            final Map<String, MultiEvaluationResult> topResults = evaluationStack.getFirst();
            Map<String, MultiEvaluationResult> nodeResults =
                new HashMap<>(topResults);
            evaluationStack.addFirst(nodeResults);
            // Analyze node
            evaluateNode(node, useUnicode, usePrettyPrinting, next, childIndexOnParnt,
                termLabelName, nodeResults, result, services);
            // Remove no longer needed child result of returned nodes
            for (int i = 0; i < iterator.getReturnedParents(); i++) {
                evaluationStack.removeFirst();
            }
        }
        return result;
    }

    /**
     * Evaluates the truth statuses changed from the parent {@link Node} to its child {@link Node}.
     *
     * @param evaluationNode The {@link Node} where the truth status tracing started.
     * @param useUnicode {@code true} use unicode characters, {@code false} do not use unicode
     *        characters.
     * @param usePrettyPrinting {@code true} use pretty printing, {@code false} do not use pretty
     *        printing.
     * @param child The current child {@link Node} to analyze.
     * @param childIndexOnParent The index of the child {@link Node} on its parent {@link Node}.
     * @param termLabelName The {@link Name} of the {@link TermLabel} to consider.
     * @param nodeResult The to child {@link Node} related result {@link Map} to update.
     * @param result The overall {@link TruthValueTracingResult} to update.
     * @param services The {@link Services} to use.
     * @throws ProofInputException Occurred exception.
     */
    private static void evaluateNode(
            final Node evaluationNode, final boolean useUnicode,
            final boolean usePrettyPrinting, final Node child, final int childIndexOnParent,
            final Name termLabelName, Map<String, MultiEvaluationResult> nodeResult,
            final TruthValueTracingResult result, final Services services)
            throws ProofInputException {
        // Analyze parent rule application
        boolean checkPerformed = false;
        if (childIndexOnParent >= 0) {
            Node parent = child.parent();
            if (parent.getAppliedRuleApp() instanceof TacletApp) {
                TacletApp tacletApp = (TacletApp) parent.getAppliedRuleApp();
                List<LabelOccurrence> labels =
                    findInvolvedLabels(parent.sequent(), tacletApp, termLabelName);
                if (!labels.isEmpty()) {
                    Taclet taclet = tacletApp.taclet();
                    if (!isClosingRule(taclet)) { // Not a closing taclet
                        checkPerformed = true;
                        TacletGoalTemplate tacletGoal =
                            taclet.goalTemplates().reverse().take(childIndexOnParent).head();
                        // Check for new minor ids created by parent rule application
                        updatePredicateResultBasedOnNewMinorIds(child, termLabelName,
                            services.getTermBuilder(), nodeResult);
                        analyzeTacletGoal(parent, tacletApp, tacletGoal, labels, services,
                            nodeResult);
                    } else if (tacletApp.posInOccurrence() != null) {
                        for (LabelOccurrence occurrence : labels) {
                            updatePredicateResult(occurrence.getLabel(),
                                !occurrence.isInAntecedent(), nodeResult);
                        }
                    }
                }
            } else if (parent.getAppliedRuleApp() instanceof OneStepSimplifierRuleApp) {
                OneStepSimplifierRuleApp app =
                    (OneStepSimplifierRuleApp) parent.getAppliedRuleApp();
                PosInOccurrence parentPio = null;
                for (RuleApp protocolApp : app.getProtocol()) {
                    if (parentPio != null) {
                        updatePredicateResultBasedOnNewMinorIdsOSS(protocolApp.posInOccurrence(),
                            parentPio, termLabelName, services.getTermBuilder(), nodeResult);
                    }
                    assert protocolApp instanceof TacletApp;
                    TacletApp tacletApp = (TacletApp) protocolApp;
                    Taclet taclet = tacletApp.taclet();
                    assert taclet.goalTemplates().size() == 1;
                    List<LabelOccurrence> labels =
                        findInvolvedLabels(parent.sequent(), tacletApp, termLabelName);
                    if (!labels.isEmpty()) {
                        analyzeTacletGoal(parent, tacletApp, taclet.goalTemplates().head(), labels,
                            services, nodeResult);
                    }
                    parentPio = protocolApp.posInOccurrence();
                }
                // Compare last PIO with PIO in child sequent (Attention: Child PIO is computed with
                // help of the PIO of the OSS)
                if (parentPio != null) {
                    assert 1 == parent.childrenCount()
                            : "Implementaton of the OneStepSimplifierRule has changed.";
                    PosInOccurrence childPio = SymbolicExecutionUtil.posInOccurrenceToOtherSequent(
                        parent, parent.getAppliedRuleApp().posInOccurrence(), parent.child(0));
                    updatePredicateResultBasedOnNewMinorIdsOSS(childPio, parentPio, termLabelName,
                        services.getTermBuilder(), nodeResult);
                }
            }
        }
        // If goal reached, update final result
        int childCount = child.childrenCount();
        if (childCount == 0) {
            Term condition =
                SymbolicExecutionUtil.computePathCondition(evaluationNode, child, false, true);
            String conditionString = SymbolicExecutionUtil.formatTerm(condition, services,
                useUnicode, usePrettyPrinting);
            result.addBranchResult(
                new BranchResult(child, nodeResult, condition, conditionString, termLabelName));
        } else if (!checkPerformed) {
            updatePredicateResultBasedOnNewMinorIds(child, termLabelName, services.getTermBuilder(),
                nodeResult);
        }
    }

    /**
     * Checks if the {@link Taclet} is a closing rule.
     *
     * @param taclet The {@link Taclet} to check.
     * @return {@code true} is closing, {@code false} is not closing.
     */
    private static boolean isClosingRule(Taclet taclet) {
        return taclet.goalTemplates().isEmpty();
    }

    /**
     * Computes the occurrences of all involved {@link FormulaTermLabel}s.
     *
     * @param sequent The {@link Sequent} on which the given {@link TacletApp} was applied.
     * @param tacletApp The applied {@link TacletApp}.
     * @param termLabelName The {@link Name} of the {@link TermLabel} to consider.
     * @return The found {@link LabelOccurrence}s.
     */
    private static List<LabelOccurrence> findInvolvedLabels(
            Sequent sequent, TacletApp tacletApp,
            Name termLabelName) {
        List<LabelOccurrence> result = new LinkedList<>();
        // Search for labels in find part
        PosInOccurrence pio = tacletApp.posInOccurrence();
        if (pio != null) {
            Term term = pio.subTerm();
            if (term != null) {
                // Check for evaluated truth values
                TermLabel label = term.getLabel(termLabelName);
                if (label instanceof FormulaTermLabel) {
                    result.add(new LabelOccurrence((FormulaTermLabel) label, pio.isInAntec()));
                }
            }
        }
        if (isClosingRule(tacletApp.taclet())) {
            if (tacletApp.ifInstsComplete() && tacletApp.ifFormulaInstantiations() != null) {
                for (IfFormulaInstantiation ifInst : tacletApp.ifFormulaInstantiations()) {
                    assert ifInst instanceof IfFormulaInstSeq;
                    Term term = ifInst.getConstrainedFormula().formula();
                    TermLabel label = term.getLabel(termLabelName);
                    if (label instanceof FormulaTermLabel) {
                        result.add(new LabelOccurrence((FormulaTermLabel) label,
                            ((IfFormulaInstSeq) ifInst).inAntec()));
                    }
                }
            }
        }
        return result;
    }

    /**
     * Utility class which specifies the occurrence of a {@link FormulaTermLabel}.
     *
     * @author Martin Hentschel
     */
    private static class LabelOccurrence {
        /**
         * The {@link FormulaTermLabel}.
         */
        private final FormulaTermLabel label;

        /**
         * {@code true} occurred in antecedent, {@code false} occurred in succedent.
         */
        private final boolean inAntecedent;

        /**
         * Constructor.
         *
         * @param label The {@link FormulaTermLabel}.
         * @param inAntecedent {@code true} occurred in antecedent, {@code false} occurred in
         *        succedent.
         */
        public LabelOccurrence(FormulaTermLabel label, boolean inAntecedent) {
            this.label = label;
            this.inAntecedent = inAntecedent;
        }

        /**
         * Returns the {@link FormulaTermLabel}.
         *
         * @return The {@link FormulaTermLabel}.
         */
        public FormulaTermLabel getLabel() {
            return label;
        }

        /**
         * Checks if the label occurred in antecedent or succedent.
         *
         * @return {@code true} occurred in antecedent, {@code false} occurred in succedent.
         */
        public boolean isInAntecedent() {
            return inAntecedent;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public String toString() {
            return label + (inAntecedent ? " in antecedent" : " in succedent");
        }
    }

    /**
     * Analyzes the given {@link TacletGoalTemplate}.
     *
     * @param parent The current {@link Node} on which the rule was applied.
     * @param tacletApp The {@link TacletApp}.
     * @param tacletGoal The {@link TacletGoalTemplate}.
     * @param labels The {@link FormulaTermLabel}s.
     * @param servies The {@link Services} to use.
     * @param results The {@link Map} with all available {@link MultiEvaluationResult}s.
     */
    private static void analyzeTacletGoal(
            Node parent, TacletApp tacletApp,
            TacletGoalTemplate tacletGoal, List<LabelOccurrence> labels, Services services,
            Map<String, MultiEvaluationResult> results) {
        Object replaceObject = tacletGoal.replaceWithExpressionAsObject();
        if (replaceObject instanceof Term) {
            Term replaceTerm = SymbolicExecutionUtil.instantiateTerm(parent, (Term) replaceObject,
                tacletApp, services);
            if (replaceTerm.op() == Junctor.TRUE) {
                // Find term is replaced by true
                for (LabelOccurrence occurrence : labels) {
                    updatePredicateResult(occurrence.getLabel(), true, results);
                }
            } else if (replaceTerm.op() == Junctor.FALSE) {
                // Find term is replaced by false
                for (LabelOccurrence occurrence : labels) {
                    updatePredicateResult(occurrence.getLabel(), false, results);
                }
            }
        }
    }

    /**
     * Updates the {@link PredicateResult}s based on minor ID changes if available in case of
     * {@link OneStepSimplifier} usage.
     *
     * @param childNode The child {@link Node}.
     * @param termLabelName The name of the {@link TermLabel} which is added to predicates.
     * @param tb The {@link TermBuilder} to use.
     * @param results The {@link Map} with all available {@link MultiEvaluationResult}s.
     */
    private static void updatePredicateResultBasedOnNewMinorIdsOSS(
            final PosInOccurrence childPio,
            final PosInOccurrence parentPio, final Name termLabelName, final TermBuilder tb,
            final Map<String, MultiEvaluationResult> results) {
        if (parentPio != null) {
            // Check application term and all of its children and grand children
            parentPio.subTerm().execPreOrder(new DefaultVisitor() {
                @Override
                public void visit(Term visited) {
                    checkForNewMinorIdsOSS(childPio.sequentFormula(), visited, termLabelName,
                        parentPio, tb, results);
                }
            });
            // Check application term parents
            PosInOccurrence currentPio = parentPio;
            while (!currentPio.isTopLevel()) {
                currentPio = currentPio.up();
                checkForNewMinorIdsOSS(childPio.sequentFormula(), currentPio.subTerm(),
                    termLabelName, parentPio, tb, results);
            }
        }
    }

    /**
     * Checks if new minor IDs are available in case of {@link OneStepSimplifier} usage.
     *
     * @param onlyChangedChildSF The only changed {@link SequentFormula} in the child {@link Node}.
     * @param term The {@link Term} contained in the child {@link Node} to check.
     * @param termLabelName The name of the {@link TermLabel} which is added to predicates.
     * @param parentPio The {@link PosInOccurrence} of the applied rule of the parent {@link Node}.
     * @param tb The {@link TermBuilder} to use.
     * @param results The {@link Map} with all available {@link MultiEvaluationResult}s.
     */
    private static void checkForNewMinorIdsOSS(
            SequentFormula onlyChangedChildSF, Term term,
            Name termLabelName, PosInOccurrence parentPio, TermBuilder tb,
            Map<String, MultiEvaluationResult> results) {
        TermLabel label = term.getLabel(termLabelName);
        if (label instanceof FormulaTermLabel) {
            Term replacement = checkForNewMinorIdsOSS(onlyChangedChildSF, (FormulaTermLabel) label,
                parentPio.isInAntec(), tb);
            if (replacement != null) {
                updatePredicateResult((FormulaTermLabel) label, replacement, results);
            }
        }
    }

    /**
     * Checks if new minor IDs are available in case of {@link OneStepSimplifier} usage.
     *
     * @param onlyChangedChildSF The only changed {@link SequentFormula} in the child {@link Node}.
     * @param label The {@link FormulaTermLabel} of interest.
     * @param antecedentRuleApplication {@code true} rule applied on antecedent, {@code false} rule
     *        applied on succedent.
     * @param tb The {@link TermBuilder} to use.
     * @return The computed instruction {@link Term} or {@code null} if not available.
     */
    private static Term checkForNewMinorIdsOSS(
            SequentFormula onlyChangedChildSF,
            FormulaTermLabel label, boolean antecedentRuleApplication, TermBuilder tb) {
        // Search replacements
        List<Term> antecedentReplacements = new LinkedList<>();
        List<Term> succedentReplacements = new LinkedList<>();
        if (antecedentRuleApplication) {
            listLabelReplacements(onlyChangedChildSF, label.name(), label.getId(),
                antecedentReplacements);
        } else {
            listLabelReplacements(onlyChangedChildSF, label.name(), label.getId(),
                succedentReplacements);
        }
        // Compute term
        return computeInstructionTerm(antecedentReplacements, succedentReplacements,
            antecedentRuleApplication, tb);
    }

    /**
     * Updates the {@link PredicateResult}s based on minor ID changes if available.
     *
     * @param childNode The child {@link Node}.
     * @param termLabelName The name of the {@link TermLabel} which is added to predicates.
     * @param tb The {@link TermBuilder} to use.
     * @param results The {@link Map} with all available {@link MultiEvaluationResult}s.
     */
    private static void updatePredicateResultBasedOnNewMinorIds(
            final Node childNode,
            final Name termLabelName, final TermBuilder tb,
            final Map<String, MultiEvaluationResult> results) {
        final Node parentNode = childNode.parent();
        if (parentNode != null) {
            final RuleApp parentRuleApp = parentNode.getAppliedRuleApp();
            final PosInOccurrence parentPio = parentRuleApp.posInOccurrence();
            if (parentPio != null) {
                // Check application term and all of its children and grand children
                parentPio.subTerm().execPreOrder(new DefaultVisitor() {
                    @Override
                    public void visit(Term visited) {
                        checkForNewMinorIds(childNode, visited, termLabelName, parentPio, tb,
                            results);
                    }
                });
                // Check application term parents
                PosInOccurrence currentPio = parentPio;
                while (!currentPio.isTopLevel()) {
                    currentPio = currentPio.up();
                    checkForNewMinorIds(childNode, currentPio.subTerm(), termLabelName, parentPio,
                        tb, results);
                }
                // Check if instantiations
                if (parentRuleApp instanceof TacletApp) {
                    TacletApp ta = (TacletApp) parentRuleApp;
                    if (ta.ifInstsComplete() && ta.ifFormulaInstantiations() != null) {
                        for (IfFormulaInstantiation ifInst : ta.ifFormulaInstantiations()) {
                            checkForNewMinorIds(childNode, ifInst.getConstrainedFormula().formula(),
                                termLabelName, parentPio, tb, results);
                        }
                    }
                }
            }
        }
    }

    /**
     * Checks if new minor IDs are available.
     *
     * @param childNode The child {@link Node}.
     * @param term The {@link Term} contained in the child {@link Node} to check.
     * @param termLabelName The name of the {@link TermLabel} which is added to predicates.
     * @param parentPio The {@link PosInOccurrence} of the applied rule of the parent {@link Node}.
     * @param tb The {@link TermBuilder} to use.
     * @param results The {@link Map} with all available {@link MultiEvaluationResult}s.
     */
    private static void checkForNewMinorIds(
            Node childNode, Term term, Name termLabelName,
            PosInOccurrence parentPio, TermBuilder tb, Map<String, MultiEvaluationResult> results) {
        TermLabel label = term.getLabel(termLabelName);
        if (label instanceof FormulaTermLabel) {
            Term replacement =
                checkForNewMinorIds(childNode, (FormulaTermLabel) label, parentPio.isInAntec(), tb);
            if (replacement != null) {
                updatePredicateResult((FormulaTermLabel) label, replacement, results);
            }
        }
    }

    /**
     * Checks if new minor IDs are available.
     *
     * @param childNode The child {@link Node}.
     * @param label The {@link FormulaTermLabel} of interest.
     * @param antecedentRuleApplication {@code true} rule applied on antecedent, {@code false} rule
     *        applied on succedent.
     * @param tb The {@link TermBuilder} to use.
     * @return The computed instruction {@link Term} or {@code null} if not available.
     */
    private static Term checkForNewMinorIds(
            Node childNode, FormulaTermLabel label,
            boolean antecedentRuleApplication, TermBuilder tb) {
        // Search replacements
        List<Term> antecedentReplacements = new LinkedList<>();
        List<Term> succedentReplacements = new LinkedList<>();
        for (SequentFormula sf : childNode.sequent().antecedent()) {
            listLabelReplacements(sf, label.name(), label.getId(), antecedentReplacements);
        }
        for (SequentFormula sf : childNode.sequent().succedent()) {
            listLabelReplacements(sf, label.name(), label.getId(), succedentReplacements);
        }
        // Compute term
        return computeInstructionTerm(antecedentReplacements, succedentReplacements,
            antecedentRuleApplication, tb);
    }

    /**
     * Lists all label replacements in the given {@link SequentFormula}.
     *
     * @param sf The {@link SequentFormula} to analyze.
     * @param labelName The name of the {@link TermLabel} which is added to predicates.
     * @param labelId The label ID of interest.
     * @param resultToFill The result {@link List} to fill.
     */
    private static void listLabelReplacements(
            final SequentFormula sf, final Name labelName,
            final String labelId, final List<Term> resultToFill) {
        sf.formula().execPreOrder(new DefaultVisitor() {
            @Override
            public boolean visitSubtree(Term visited) {
                return !hasLabelOfInterest(visited);
            }

            @Override
            public void visit(Term visited) {
                if (hasLabelOfInterest(visited)) {
                    resultToFill.add(visited);
                }
            }

            private boolean hasLabelOfInterest(Term visited) {
                TermLabel visitedLabel = visited.getLabel(labelName);
                if (visitedLabel instanceof FormulaTermLabel) {
                    FormulaTermLabel pLabel = (FormulaTermLabel) visitedLabel;
                    String[] beforeIds = pLabel.getBeforeIds();
                    return ArrayUtil.contains(beforeIds, labelId);
                } else {
                    return false;
                }
            }
        });
    }

    /**
     * Computes the {@link Term} with the instruction how to compute the truth value based on the
     * found replacements.
     *
     * @param antecedentReplacements The replacements found in the antecedent.
     * @param succedentReplacements The replacements found in the succedent.
     * @param antecedentRuleApplication {@code true} rule applied on antecedent, {@code false} rule
     *        applied on succedent.
     * @param tb The {@link TermBuilder} to use.
     * @return The computed instruction {@link Term} or {@code null} if not available.
     */
    private static Term computeInstructionTerm(
            List<Term> antecedentReplacements,
            List<Term> succedentReplacements, boolean antecedentRuleApplication, TermBuilder tb) {
        if (!antecedentReplacements.isEmpty() || !succedentReplacements.isEmpty()) {
            Term left = tb.andPreserveLabels(antecedentReplacements);
            Term right = tb.orPreserveLabels(succedentReplacements);
            if (antecedentRuleApplication) {
                return tb.andPreserveLabels(left, tb.notPreserveLabels(right));
            } else {
                return tb.impPreserveLabels(left, right);
            }
        } else {
            return null;
        }
    }

    /**
     * Updates the instruction {@link Term} for the given {@link FormulaTermLabel} in the result
     * {@link Map}.
     *
     * @param label The {@link FormulaTermLabel} to update its instruction {@link Term}.
     * @param instructionTerm The new instruction {@link Term} to set.
     * @param results The {@link Map} with all available {@link MultiEvaluationResult}s.
     */
    private static void updatePredicateResult(
            FormulaTermLabel label, Term instructionTerm,
            Map<String, MultiEvaluationResult> results) {
        MultiEvaluationResult result = results.get(label.getId());
        if (result == null) {
            result = new MultiEvaluationResult(instructionTerm);
        } else {
            result = result.newInstructionTerm(instructionTerm);
        }
        results.put(label.getId(), result);
    }

    /**
     * Updates the evaluation result for the given {@link FormulaTermLabel} in the result
     * {@link Map}.
     *
     * @param label The {@link FormulaTermLabel} to update its instruction {@link Term}.
     * @param evaluationResult {@code true} label evaluates at least once to true, {@code false}
     *        label evaluates at least once to false.
     * @param results The {@link Map} with all available {@link MultiEvaluationResult}s.
     */
    private static void updatePredicateResult(
            FormulaTermLabel label, boolean evaluationResult,
            Map<String, MultiEvaluationResult> results) {
        MultiEvaluationResult result = results.get(label.getId());
        if (result == null) {
            result = new MultiEvaluationResult(evaluationResult);
        } else {
            result = result.newEvaluationResult(evaluationResult);
        }
        results.put(label.getId(), result);
    }

    /**
     * Instances of this unmodifyable class are used to store the found evaluation results.
     *
     * @author Martin Hentschel
     */
    public static class MultiEvaluationResult {
        /**
         * {@code true} label evaluates at least once to true, {@code false} label never evaluates
         * to true.
         */
        private final boolean evaluatesToTrue;

        /**
         * {@code true} label evaluates at least once to false, {@code false} label never evaluates
         * to false.
         */
        private final boolean evaluatesToFalse;

        /**
         * The instruction {@link Term}.
         */
        private final Term instructionTerm;

        /**
         * Constructor.
         *
         * @param evaluationResult {@code true} label evaluates at least once to true, {@code false}
         *        label evaluates at least once to false.
         */
        public MultiEvaluationResult(boolean evaluationResult) {
            this(evaluationResult, !evaluationResult, null);
        }

        /**
         * Constructor.
         *
         * @param instructionTerm The instruction {@link Term}.
         */
        public MultiEvaluationResult(Term instructionTerm) {
            this(false, false, instructionTerm);
        }

        /**
         * Constructor.
         *
         * @param evaluatesToTrue {@code true} label evaluates at least once to true, {@code false}
         *        label never evaluates to true.
         * @param evaluatesToFalse {@code true} label evaluates at least once to false,
         *        {@code false} label never evaluates to false.
         * @param instructionTerm The instruction {@link Term}.
         */
        public MultiEvaluationResult(boolean evaluatesToTrue, boolean evaluatesToFalse,
                Term instructionTerm) {
            this.evaluatesToTrue = evaluatesToTrue;
            this.evaluatesToFalse = evaluatesToFalse;
            this.instructionTerm = instructionTerm;
        }

        /**
         * Checks if it is at least once evaluated to {@code true}.
         *
         * @return {@code true} label evaluates at least once to true, {@code false} label never
         *         evaluates to true.
         */
        public boolean isEvaluatesToTrue() {
            return evaluatesToTrue;
        }

        /**
         * Checks if it is at least once evaluated to {@code false}.
         *
         * @return {@code true} label evaluates at least once to false, {@code false} label never
         *         evaluates to false.
         */
        public boolean isEvaluatesToFalse() {
            return evaluatesToFalse;
        }

        /**
         * Returns the instruction {@link Term}.
         *
         * @return The instruction {@link Term} or {@code null} if undefined.
         */
        public Term getInstructionTerm() {
            return instructionTerm;
        }

        /**
         * Creates a new {@link MultiEvaluationResult} based on the current once but with an updated
         * evaluation result.
         *
         * @param evaluationResult {@code true} label evaluates at least once to true, {@code false}
         *        label evaluates at least once to false.
         * @return The new created {@link MultiEvaluationResult}.
         */
        public MultiEvaluationResult newEvaluationResult(boolean evaluationResult) {
            if (evaluationResult) {
                return newEvaluatesToTrue(true);
            } else {
                return newEvaluatesToFalse(true);
            }
        }

        /**
         * Creates a new {@link MultiEvaluationResult} based on the current once but with an update
         * evaluates to true state.
         *
         * @param newEvaluatesToTrue {@code true} label evaluates at least once to true,
         *        {@code false} label never evaluates to true.
         * @return The new created {@link MultiEvaluationResult}.
         */
        public MultiEvaluationResult newEvaluatesToTrue(boolean newEvaluatesToTrue) {
            return new MultiEvaluationResult(newEvaluatesToTrue, evaluatesToFalse, instructionTerm);
        }

        /**
         * Creates a new {@link MultiEvaluationResult} based on the current once but with an update
         * evaluates to false state.
         *
         * @param newEvaluatesToFalse {@code true} label evaluates at least once to false,
         *        {@code false} label never evaluates to false.
         * @return The new created {@link MultiEvaluationResult}.
         */
        public MultiEvaluationResult newEvaluatesToFalse(boolean newEvaluatesToFalse) {
            return new MultiEvaluationResult(evaluatesToTrue, newEvaluatesToFalse, instructionTerm);
        }

        /**
         * Creates a new {@link MultiEvaluationResult} based on the current once but with an update
         * instruction term.
         *
         * @param newInstructionTerm The new instruction {@link Term}.
         * @return The new created {@link MultiEvaluationResult}.
         */
        public MultiEvaluationResult newInstructionTerm(Term newInstructionTerm) {
            return new MultiEvaluationResult(evaluatesToTrue, evaluatesToFalse, newInstructionTerm);
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public String toString() {
            return "true=" + evaluatesToTrue + ", false=" + evaluatesToFalse + ", instruction="
                + instructionTerm;
        }

        /**
         * Creates a pretty printed {@link String}.
         *
         * @param services The {@link Services} to use.
         * @return The pretty printed {@link String}.
         */
        public String toPrettyString(Services services) {
            return "true=" + evaluatesToTrue + ", false=" + evaluatesToFalse
                + (instructionTerm != null
                        ? ", instruction:\n" + ProofSaver.printTerm(instructionTerm, services)
                        : "");
        }

        /**
         * Computes the final truth value.
         *
         * @param termLabelName The {@link Name} of the {@link TermLabel} to consider.
         * @param results All available {@link MultiEvaluationResult}s.
         * @return The computed {@link TruthValue}.
         */
        public TruthValue evaluate(Name termLabelName, Map<String, MultiEvaluationResult> results) {
            if (evaluatesToTrue && evaluatesToFalse) {
                return TruthValue.UNKNOWN;
            } else if (evaluatesToTrue) {
                return TruthValue.TRUE;
            } else if (evaluatesToFalse) {
                return TruthValue.FALSE;
            } else if (instructionTerm != null) {
                return evaluateTerm(instructionTerm, termLabelName, results);
            } else {
                return TruthValue.UNKNOWN;
            }
        }

        /***
         * Computes the {@link TruthValue} of the given instruction {@link Term}.
         *
         * @param term The instruction {@link Term} to evaluate.
         * @param termLabelName The {@link Name} of the {@link TermLabel} to consider.
         * @param results All available {@link MultiEvaluationResult}s.
         * @return The computed {@link TruthValue}.
         */
        private static TruthValue evaluateTerm(Term term, Name termLabelName,
                Map<String, MultiEvaluationResult> results) {
            TermLabel label = term.getLabel(termLabelName);
            // Return direct label result if available
            if (label instanceof FormulaTermLabel) {
                MultiEvaluationResult instruction = results.get(((FormulaTermLabel) label).getId());
                if (instruction != null) {
                    return instruction.evaluate(termLabelName, results);
                }
            }
            // If direct label result is not available try to compute it. (e.g. because of or/and
            // label was replaced by sequent top level formuals)
            if (term.op() == Junctor.AND || term.op() == Junctor.IMP || term.op() == Junctor.OR
                    || term.op() == Equality.EQV) {
                Term leftTerm = TermBuilder.goBelowUpdates(term.sub(0));
                Term rightTerm = TermBuilder.goBelowUpdates(term.sub(1));
                TermLabel leftLabel = leftTerm.getLabel(termLabelName);
                TermLabel rightLabel = rightTerm.getLabel(termLabelName);
                MultiEvaluationResult leftInstruction = leftLabel instanceof FormulaTermLabel
                        ? results.get(((FormulaTermLabel) leftLabel).getId())
                        : null;
                MultiEvaluationResult rightInstruction = rightLabel instanceof FormulaTermLabel
                        ? results.get(((FormulaTermLabel) rightLabel).getId())
                        : null;
                TruthValue leftValue =
                    leftInstruction != null ? leftInstruction.evaluate(termLabelName, results)
                            : evaluateTerm(leftTerm, termLabelName, results);
                TruthValue rightValue =
                    rightInstruction != null ? rightInstruction.evaluate(termLabelName, results)
                            : evaluateTerm(rightTerm, termLabelName, results);
                TruthValue resultValue;
                if (term.op() == Junctor.AND) {
                    resultValue = TruthValue.and(leftValue, rightValue);
                } else if (term.op() == Junctor.IMP) {
                    resultValue = TruthValue.imp(leftValue, rightValue);
                } else if (term.op() == Junctor.OR) {
                    resultValue = TruthValue.or(leftValue, rightValue);
                } else if (term.op() == Equality.EQV) {
                    resultValue = TruthValue.eqv(leftValue, rightValue);
                } else {
                    throw new IllegalStateException(
                        "Operator '" + term.op() + "' is not supported.");
                }
                return resultValue;
            } else if (term.op() == Junctor.NOT) {
                Term argumentTerm = TermBuilder.goBelowUpdates(term.sub(0));
                TermLabel argumentLabel = argumentTerm.getLabel(termLabelName);
                MultiEvaluationResult argumentInstruction =
                    argumentLabel instanceof FormulaTermLabel
                            ? results.get(((FormulaTermLabel) argumentLabel).getId())
                            : null;
                TruthValue argumentValue = argumentInstruction != null
                        ? argumentInstruction.evaluate(termLabelName, results)
                        : evaluateTerm(argumentTerm, termLabelName, results);
                TruthValue resultValue = TruthValue.not(argumentValue);
                return resultValue;
            } else if (term.op() == Junctor.TRUE) {
                return TruthValue.TRUE;
            } else if (term.op() == Junctor.FALSE) {
                return TruthValue.FALSE;
            } else if (isIfThenElseFormula(term)) {
                Term conditionTerm = TermBuilder.goBelowUpdates(term.sub(0));
                Term thenTerm = TermBuilder.goBelowUpdates(term.sub(1));
                Term elseTerm = TermBuilder.goBelowUpdates(term.sub(2));
                TermLabel conditionLabel = conditionTerm.getLabel(termLabelName);
                TermLabel thenLabel = thenTerm.getLabel(termLabelName);
                TermLabel elseLabel = elseTerm.getLabel(termLabelName);
                MultiEvaluationResult conditionInstruction =
                    conditionLabel instanceof FormulaTermLabel
                            ? results.get(((FormulaTermLabel) conditionLabel).getId())
                            : null;
                MultiEvaluationResult thenInstruction = thenLabel instanceof FormulaTermLabel
                        ? results.get(((FormulaTermLabel) thenLabel).getId())
                        : null;
                MultiEvaluationResult elseInstruction = elseLabel instanceof FormulaTermLabel
                        ? results.get(((FormulaTermLabel) elseLabel).getId())
                        : null;
                TruthValue conditionValue = conditionInstruction != null
                        ? conditionInstruction.evaluate(termLabelName, results)
                        : evaluateTerm(conditionTerm, termLabelName, results);
                TruthValue thenValue =
                    thenInstruction != null ? thenInstruction.evaluate(termLabelName, results)
                            : evaluateTerm(thenTerm, termLabelName, results);
                TruthValue elseValue =
                    elseInstruction != null ? elseInstruction.evaluate(termLabelName, results)
                            : evaluateTerm(elseTerm, termLabelName, results);
                TruthValue resultValue =
                    TruthValue.ifThenElse(conditionValue, thenValue, elseValue);
                return resultValue;
            } else {
                return null;
            }
        }
    }

    /**
     * Represents the final predicate evaluation result returned by
     * {@link TruthValueEvaluationUtil#evaluate(Node, Name, boolean, boolean).
     *
     * @author Martin Hentschel
     */
    public static class TruthValueTracingResult {
        /**
         * The {@link BranchResult}s.
         */
        private final List<BranchResult> branchResults = new LinkedList<>();

        /**
         * Adds a {@link BranchResult}.
         *
         * @param result The {@link BranchResult} to add.
         */
        public void addBranchResult(BranchResult result) {
            if (result != null) {
                branchResults.add(result);
            }
        }

        /**
         * Returns all {@link BranchResult}s.
         *
         * @return The {@link BranchResult}s.
         */
        public BranchResult[] getBranchResults() {
            return branchResults.toArray(new BranchResult[branchResults.size()]);
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public String toString() {
            StringBuilder sb = new StringBuilder();
            boolean afterFirst = false;
            for (BranchResult result : branchResults) {
                if (afterFirst) {
                    sb.append("\n\n");
                } else {
                    afterFirst = true;
                }
                sb.append(result);
            }
            return sb.toString();
        }
    }

    /**
     * Represents the unmodifiable predicate results of a leaf {@link Node} ({@link Goal}).
     *
     * @author Martin Hentschel
     */
    public static class BranchResult {
        /**
         * All found results.
         */
        private final Map<String, MultiEvaluationResult> results;

        /**
         * The leaf {@link Node}.
         */
        private final Node leafNode;

        /**
         * The condition under which the leaf {@link Node} is reached from the analyzed
         * {@link Node}.
         */
        private final Term condition;

        /**
         * The human readable condition under which the leaf {@link Node} is reached from the
         * analyzed {@link Node}.
         */
        private final String conditionString;

        /**
         * The {@link Name} of the {@link TermLabel} to consider.
         */
        private final Name termLabelName;

        /**
         * Constructor.
         *
         * @param leafNode The leaf {@link Node}.
         * @param results All found results.
         * @param condition The condition under which the leaf {@link Node} is reached from the
         *        analyzed {@link Node}.
         * @param conditionString The human readable condition under which the leaf {@link Node} is
         *        reached from the analyzed {@link Node}.
         * @param termLabelName The {@link Name} of the {@link TermLabel} to consider.
         */
        public BranchResult(Node leafNode, Map<String, MultiEvaluationResult> results,
                Term condition, String conditionString, Name termLabelName) {
            assert leafNode != null;
            assert results != null;
            assert termLabelName != null;
            this.leafNode = leafNode;
            this.results = results;
            this.condition = condition;
            this.conditionString = conditionString;
            this.termLabelName = termLabelName;
        }

        /**
         * Returns all found results.
         *
         * @return All found results.
         */
        public Map<String, MultiEvaluationResult> getResults() {
            return Collections.unmodifiableMap(results);
        }

        /**
         * Returns the {@link MultiEvaluationResult} for the given {@link FormulaTermLabel}.
         *
         * @param termLabel The {@link FormulaTermLabel}.
         * @return The found {@link MultiEvaluationResult} or {@code null} if not available.
         */
        public MultiEvaluationResult getResult(FormulaTermLabel termLabel) {
            return termLabel != null ? results.get(termLabel.getId()) : null;
        }

        /**
         * Updates a result.
         * <p>
         * <b>Warning: </b> {@link BranchResult}s are considered to be unmodifiable. This means that
         * an update of the result needs to be done before results are shown to the user by the UI.
         *
         * @param termLabel The {@link FormulaTermLabel} to update.
         * @param result The new result of the given {@link FormulaTermLabel}.
         */
        public void updateResult(FormulaTermLabel termLabel, MultiEvaluationResult result) {
            if (termLabel != null) {
                results.put(termLabel.getId(), result);
            }
        }

        /**
         * Returns the condition under which the leaf {@link Node} is reached from the analyzed
         * {@link Node}.
         *
         * @return The condition under which the leaf {@link Node} is reached from the analyzed
         *         {@link Node}.
         */
        public Term getCondition() {
            return condition;
        }

        /**
         * Returns the human readable condition under which the leaf {@link Node} is reached from
         * the analyzed {@link Node}.
         *
         * @return The human readable condition under which the leaf {@link Node} is reached from
         *         the analyzed {@link Node}.
         */
        public String getConditionString() {
            return conditionString;
        }

        /**
         * Returns the {@link Name} of the {@link TermLabel} to consider.
         *
         * @return The {@link Name} of the {@link TermLabel} to consider.
         */
        public Name getTermLabelName() {
            return termLabelName;
        }

        /**
         * Checks if the {@link Term} has a {@link TermLabel} with {@link Name}
         * {@link #getTermLabelName()}.
         *
         * @param term The {@link Term} to check.
         * @return {@code true} has {@link TermLabel}, {@code false} do not has {@link TermLabel}.
         */
        public boolean hasPredicateLabel(Term term) {
            return getPredicateLabel(term) != null;
        }

        /**
         * Returns the first {@link FormulaTermLabel} with {@link Name} {@link #getTermLabelName()}.
         *
         * @param term The {@link Term}.
         * @return The found {@link FormulaTermLabel} or {@code null} otherwise.
         */
        public FormulaTermLabel getPredicateLabel(Term term) {
            TermLabel label = term.getLabel(termLabelName);
            return label instanceof FormulaTermLabel ? (FormulaTermLabel) label : null;
        }

        /**
         * Returns the leaf {@link Node}.
         *
         * @return The leaf {@link Node}.
         */
        public Node getLeafNode() {
            return leafNode;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public String toString() {
            StringBuilder sb = new StringBuilder();
            sb.append("Goal ");
            sb.append(leafNode.serialNr());
            sb.append("\n");
            boolean afterFirst = false;
            for (Entry<String, MultiEvaluationResult> entry : results.entrySet()) {
                if (afterFirst) {
                    sb.append("\n");
                } else {
                    afterFirst = true;
                }
                sb.append(entry.getKey());
                sb.append(" = ");
                sb.append(entry.getValue().evaluate(termLabelName, results));
                sb.append(" :: ");
                sb.append(entry.getValue());
            }
            return sb.toString();
        }

        /**
         * Creates a pretty printed {@link String}.
         *
         * @return The pretty printed {@link String}.
         */
        public String toPrettyString() {
            StringBuilder sb = new StringBuilder();
            sb.append("Goal ");
            sb.append(leafNode.serialNr());
            sb.append("\n");
            boolean afterFirst = false;
            for (Entry<String, MultiEvaluationResult> entry : results.entrySet()) {
                if (afterFirst) {
                    sb.append("\n");
                } else {
                    afterFirst = true;
                }
                sb.append(entry.getKey());
                sb.append(" = ");
                sb.append(entry.getValue().evaluate(termLabelName, results));
                sb.append(" :: ");
                sb.append(entry.getValue().toPrettyString(leafNode.proof().getServices()));
            }
            return sb.toString();
        }

        /**
         * Evaluates the given {@link FormulaTermLabel}.
         *
         * @param termLabel The {@link FormulaTermLabel} to evaluate.
         * @return The evaluation result.
         */
        public TruthValue evaluate(FormulaTermLabel termLabel) {
            if (termLabel != null) {
                MultiEvaluationResult instruction = getResult(termLabel);
                return instruction != null ? instruction.evaluate(termLabelName, results) : null;
            } else {
                return null;
            }
        }
    }

    /**
     * Represents the possible truth values.
     *
     * @author Martin Hentschel
     */
    public enum TruthValue {
        /**
         * True.
         */
        TRUE,

        /**
         * False.
         */
        FALSE,

        /**
         * Unknown in cases:
         * <ul>
         * <li>Predicate evaluates to true and false.</li>
         * <li>Predicate is dropped without evaluation.</li>
         * <li>Predicate is never evaluated.</li>
         * </ul>
         */
        UNKNOWN;

        /**
         * {@inheritDoc}
         *
         * @return
         */
        @Override
        public String toString() {
            if (this == TRUE) {
                return "true";
            } else if (this == FALSE) {
                return "false";
            } else {
                return "unknown";
            }
        }

        /**
         * Computes the {@code and} value.
         *
         * @param left The left {@link TruthValue}.
         * @param right The right {@link TruthValue}.
         * @return The computed {@code and} value.
         */
        public static TruthValue and(TruthValue left, TruthValue right) {
            if (left == null || UNKNOWN.equals(left)) {
                if (FALSE.equals(right)) {
                    return FALSE;
                } else {
                    return UNKNOWN;
                }
            } else if (right == null || UNKNOWN.equals(right)) {
                if (FALSE.equals(left)) {
                    return FALSE;
                } else {
                    return UNKNOWN;
                }
            } else {
                if (TRUE.equals(left) && TRUE.equals(right)) {
                    return TRUE;
                } else {
                    return FALSE;
                }
            }
        }

        /**
         * Computes the {@code imp} value.
         *
         * @param left The left {@link TruthValue}.
         * @param right The right {@link TruthValue}.
         * @return The computed {@code imp} value.
         */
        public static TruthValue imp(TruthValue left, TruthValue right) {
            return or(not(left), right);
        }

        /**
         * Computes the {@code or} value.
         *
         * @param left The left {@link TruthValue}.
         * @param right The right {@link TruthValue}.
         * @return The computed {@code or} value.
         */
        public static TruthValue or(TruthValue left, TruthValue right) {
            if (left == null || UNKNOWN.equals(left)) {
                if (TRUE.equals(right)) {
                    return TRUE;
                } else {
                    return UNKNOWN;
                }
            } else if (right == null || UNKNOWN.equals(right)) {
                if (TRUE.equals(left)) {
                    return TRUE;
                } else {
                    return UNKNOWN;
                }
            } else {
                if (TRUE.equals(left) || TRUE.equals(right)) {
                    return TRUE;
                } else {
                    return FALSE;
                }
            }
        }

        /**
         * Computes the {@code not} value.
         *
         * @param value The {@link TruthValue}.
         * @return The computed {@code not} value.
         */
        public static TruthValue not(TruthValue value) {
            if (TRUE.equals(value)) {
                return FALSE;
            } else if (FALSE.equals(value)) {
                return TRUE;
            } else {
                return UNKNOWN;
            }
        }

        /**
         * Computes the {@code eqv} value.
         *
         * @param value The {@link TruthValue}.
         * @return The computed {@code not} value.
         */
        public static TruthValue eqv(TruthValue left, TruthValue right) {
            return or(and(left, right), and(not(left), not(right)));
        }

        /**
         * Computes the {@code if-then-else} value.
         *
         * @param conditionValue The condition value.
         * @param thenValue The then value.
         * @param elseValue The else value.
         * @return The computed {@code if-then-else} value.
         */
        public static TruthValue ifThenElse(TruthValue conditionValue, TruthValue thenValue,
                TruthValue elseValue) {
            if (TRUE.equals(conditionValue)) {
                return thenValue;
            } else if (FALSE.equals(conditionValue)) {
                return elseValue;
            } else {
                return UNKNOWN;
            }
        }
    }
}

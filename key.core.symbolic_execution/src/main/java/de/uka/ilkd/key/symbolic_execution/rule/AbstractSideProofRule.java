/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.rule;

import java.util.Deque;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionSideProofUtil;

import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.logic.PosInTerm;
import org.key_project.logic.op.Function;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.Pair;

/**
 * Provides the basic functionality of {@link BuiltInRule} which computes something in a side proof.
 *
 * @author Martin Hentschel
 */
public abstract class AbstractSideProofRule implements BuiltInRule {
    /**
     * <p>
     * Creates a constant which is used in the original {@link Proof} to store the computed result
     * in form of {@code QueryResult = ...}
     * </p>
     * <p>
     * The used name is registered in the {@link Namespace} of the {@link Services}.
     * </p>
     *
     * @param services The {@link Services} to use-
     * @param sort The {@link Sort} to use.
     * @return The created constant.
     */
    protected Function createResultConstant(Services services, Sort sort) {
        String functionName = services.getTermBuilder().newName("QueryResult");
        Function function = new JFunction(new Name(functionName), sort);
        services.getNamespaces().functions().addSafely(function);
        return function;
    }

    /**
     * Creates the result {@link JFunction} used in a predicate to compute the result in the
     * side
     * proof.
     *
     * @param services The {@link Services} to use.
     * @param sort The {@link Sort} to use.
     * @return The created result {@link JFunction}.
     */
    protected Function createResultFunction(Services services, Sort sort) {
        return new JFunction(new Name(services.getTermBuilder().newName("ResultPredicate")),
            JavaDLTheory.FORMULA, sort);
    }

    /**
     * <p>
     * Starts the side proof and extracts the result {@link JTerm} and conditions.
     * </p>
     * <p>
     * New used names are automatically added to the {@link Namespace} of the {@link Services}.
     * </p>
     *
     * @param goal The {@link Goal} on which this {@link BuiltInRule} should be applied on.
     * @param sideProofEnvironment The given {@link ProofEnvironment} of the side proof.
     * @param sequentToProve The {@link Sequent} to prove in a side proof.
     * @param newPredicate The {@link JFunction} which is used to compute the result.
     * @return The found result {@link JTerm} and the conditions.
     * @throws ProofInputException Occurred Exception.
     */
    protected List<ResultsAndCondition> computeResultsAndConditions(Goal goal,
            ProofEnvironment sideProofEnvironment, Sequent sequentToProve,
            Function newPredicate) throws ProofInputException {
        return SymbolicExecutionSideProofUtil.computeResultsAndConditions(goal.getOverlayServices(),
            goal.proof(),
            sideProofEnvironment, sequentToProve, newPredicate,
            "Side proof rule on node " + goal.node().serialNr() + ".",
            StrategyProperties.METHOD_CONTRACT, StrategyProperties.LOOP_INVARIANT,
            StrategyProperties.QUERY_ON, StrategyProperties.SPLITTING_DELAYED, true);
    }

    /**
     * Replaces the {@link JTerm} defined by the given {@link PosInOccurrence} with the given new
     * {@link JTerm}.
     *
     * @param pio The {@link PosInOccurrence} which defines the {@link JTerm} to replace.
     * @param newTerm The new {@link JTerm}.
     * @return The created {@link SequentFormula} in which the {@link JTerm} is replaced.
     */
    protected static SequentFormula replace(PosInOccurrence pio,
            JTerm newTerm, Services services) {
        // Iterate along the PosInOccurrence and collect the parents and indices
        Deque<Pair<Integer, JTerm>> indexAndParents = new LinkedList<>();
        JTerm root = (JTerm) pio.sequentFormula().formula();
        final PosInTerm pit = pio.posInTerm();
        for (int i = 0, sz = pit.depth(); i < sz; i++) {
            int next = pit.getIndexAt(i);
            indexAndParents.addFirst(new Pair<>(next, root));
            root = root.sub(next);
        }
        // Iterate over the collected parents and replace terms
        root = newTerm;
        for (Pair<Integer, JTerm> pair : indexAndParents) {
            JTerm parent = pair.second;
            JTerm[] newSubs = parent.subs().toArray(new JTerm[parent.arity()]);
            newSubs[pair.first] = root;
            root = services.getTermFactory().createTerm(parent.op(), newSubs, parent.boundVars(),
                parent.getLabels());
        }
        return new SequentFormula(root);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

}

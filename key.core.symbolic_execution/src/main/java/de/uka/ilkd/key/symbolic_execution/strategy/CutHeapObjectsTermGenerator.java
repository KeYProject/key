/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.strategy;

import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.logic.Term;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.termgenerator.TermGenerator;

/**
 * This {@link TermGenerator} is used by the {@link SymbolicExecutionStrategy} to add early alias
 * checks of used objects as target of store operations on heaps. To achieve this, this
 * {@link TermGenerator} generates equality {@link JTerm}s for each possible combination of objects.
 *
 * @author Martin Hentschel
 */
public class CutHeapObjectsTermGenerator implements TermGenerator<Goal> {
    /**
     * {@inheritDoc}
     */
    @Override
    public Iterator<Term> generate(RuleApp app, PosInOccurrence pos,
            Goal goal,
            MutableState mState) {
        // Compute collect terms of sequent formulas
        Sequent sequent = goal.sequent();
        Set<Term> topTerms = new LinkedHashSet<>();
        for (final SequentFormula sf : sequent) {
            topTerms.add(sf.formula());
        }
        // Compute equality terms
        HeapLDT heapLDT = goal.node().proof().getServices().getTypeConverter().getHeapLDT();
        Set<Term> equalityTerms = new LinkedHashSet<>();
        for (final SequentFormula sf : sequent) {
            collectEqualityTerms(sf, equalityTerms, topTerms, heapLDT,
                goal.node().proof().getServices());
        }
        return equalityTerms.iterator();
    }

    /**
     * Computes all possible equality terms between objects in the given {@link SequentFormula}.
     *
     * @param sf The {@link SequentFormula} to work with.
     * @param equalityTerms The result {@link Set} with the equality {@link JTerm}s to fill.
     * @param topTerms The terms of all sequent formulas
     * @param heapLDT The {@link HeapLDT} to use.
     * @param services TODO
     */
    protected void collectEqualityTerms(SequentFormula sf,
            Set<Term> equalityTerms,
            Set<Term> topTerms, HeapLDT heapLDT, Services services) {
        // Collect objects (target of store operations on heap)
        Set<Term> storeLocations = new LinkedHashSet<>();
        collectStoreLocations(sf.formula(), storeLocations, heapLDT);
        // Check if equality checks are possible
        if (storeLocations.size() >= 2) {
            // Generate all possible equality checks
            JTerm[] storeLocationsArray = storeLocations.toArray(new JTerm[0]);
            for (int i = 0; i < storeLocationsArray.length; i++) {
                for (int j = i + 1; j < storeLocationsArray.length; j++) {
                    JTerm equality = services.getTermBuilder().equals(storeLocationsArray[i],
                        storeLocationsArray[j]);
                    if (!topTerms.contains(equality)) {
                        // The not is because the order of the branches is nicer (assumption:
                        // default case that objects are different is shown in symbolic execution
                        // trees on the left)
                        JTerm negatedEquality = services.getTermBuilder().not(equality);
                        if (!topTerms.contains(negatedEquality)) {
                            // Do equality cut only if knowledge is not already part of the sequent
                            equalityTerms.add(negatedEquality);
                        }
                    }
                }
            }
        }
    }

    /**
     * Collects recursive all possible targets of store operations on a heap.
     *
     * @param term The {@link JTerm} to start search in.
     * @param storeLocations The result {@link Set} to fill.
     * @param heapLDT The {@link HeapLDT} to use (it provides the store and create
     *        {@link JFunction}).
     */
    protected void collectStoreLocations(Term term,
            final Set<Term> storeLocations,
            final HeapLDT heapLDT) {
        term.execPreOrder((DefaultVisitor) visited -> {
            if (visited.op() == heapLDT.getStore()) {
                storeLocations.add(visited.sub(1));
            }
        });
    }
}

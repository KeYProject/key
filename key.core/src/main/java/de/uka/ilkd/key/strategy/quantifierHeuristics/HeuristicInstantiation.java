/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.Iterator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.termgenerator.TermGenerator;


public class HeuristicInstantiation implements TermGenerator<Goal> {

    public final static TermGenerator<Goal> INSTANCE = new HeuristicInstantiation();

    private HeuristicInstantiation() {}

    @Override
    public Iterator<Term> generate(RuleApp app, PosInOccurrence pos, Goal goal,
            MutableState mState) {
        assert pos != null : "Feature is only applicable to rules with find";

        final Term qf = pos.sequentFormula().formula();
        final Instantiation ia =
            Instantiation.create(qf, goal.sequent(), goal.proof().getServices());
        final QuantifiableVariable var = qf.varsBoundHere(0).last();
        assert var != null;
        return new HIIterator(ia.getSubstitution().iterator(), var, goal.proof().getServices());
    }


    private static class HIIterator implements Iterator<Term> {
        private final Iterator<Term> instances;

        private final Sort quantifiedVarSort;
        private final Function quantifiedVarSortCast;

        private Term nextInst = null;
        private final TermServices services;

        private HIIterator(Iterator<Term> it, QuantifiableVariable var, Services services) {
            this.instances = it;
            this.services = services;
            quantifiedVarSort = var.sort();
            quantifiedVarSortCast =
                services.getJavaDLTheory().getCastSymbol(quantifiedVarSort, services);
            findNextInst();
        }

        private void findNextInst() {
            while (nextInst == null && instances.hasNext()) {
                nextInst = instances.next();
                if (!nextInst.sort().extendsTrans(quantifiedVarSort)) {
                    if (!quantifiedVarSort.extendsTrans(nextInst.sort())) {
                        nextInst = null;
                        continue;
                    }
                    nextInst = services.getTermBuilder().func(quantifiedVarSortCast,
                        (JTerm) nextInst);
                }
            }
        }

        @Override
        public boolean hasNext() {
            return nextInst != null;
        }

        @Override
        public Term next() {
            final Term res = nextInst;
            nextInst = null;
            findNextInst();
            return res;
        }

        @Override
        public void remove() {
            throw new UnsupportedOperationException();
        }
    }

}

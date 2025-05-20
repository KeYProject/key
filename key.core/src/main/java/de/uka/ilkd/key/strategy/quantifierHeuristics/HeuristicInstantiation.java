/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.Iterator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.feature.MutableState;
import de.uka.ilkd.key.strategy.termgenerator.TermGenerator;

import org.key_project.logic.sort.Sort;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;


public class HeuristicInstantiation implements TermGenerator {

    public final static TermGenerator INSTANCE = new HeuristicInstantiation();

    private HeuristicInstantiation() {}

    @Override
    public @NonNull Iterator<Term> generate(RuleApp app, @NonNull PosInOccurrence pos,
            @NonNull Goal goal,
            MutableState mState) {
        assert pos != null : "Feature is only applicable to rules with find";

        final Term qf = pos.sequentFormula().formula();
        final Instantiation ia =
            Instantiation.create(qf, goal.sequent(), goal.proof().getServices());
        final QuantifiableVariable var = qf.varsBoundHere(0).last();
        return new HIIterator(ia.getSubstitution().iterator(), var, goal.proof().getServices());
    }


    private static class HIIterator implements Iterator<Term> {
        private final Iterator<Term> instances;

        private final QuantifiableVariable quantifiedVar;

        private final @NonNull Sort quantifiedVarSort;
        private final @NonNull JFunction quantifiedVarSortCast;

        private @Nullable Term nextInst = null;
        private final @NonNull TermServices services;

        private HIIterator(Iterator<Term> it, QuantifiableVariable var,
                @NonNull Services services) {
            this.instances = it;
            this.quantifiedVar = var;
            this.services = services;
            quantifiedVarSort = quantifiedVar.sort();
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
                    nextInst = services.getTermBuilder().func(quantifiedVarSortCast, nextInst);
                }
            }
        }

        public boolean hasNext() {
            return nextInst != null;
        }

        public @Nullable Term next() {
            final Term res = nextInst;
            nextInst = null;
            findNextInst();
            return res;
        }

        public void remove() {
            throw new UnsupportedOperationException();
        }
    }

}

/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.op.*;

import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSet;

/**
 * This class is used to select and store <code>Trigger</code>s for a quantified formula in Prenex
 * CNF(PCNF).
 */
public class TriggersSet {

    /** Quantified formula of PCNF */
    private final JTerm allTerm;
    /** all <code>Trigger</code>s for <code>allTerm</code> */
    private ImmutableSet<Trigger> allTriggers = DefaultImmutableSet.nil();
    /**
     * a <code>HashMap</code> from <code>Term</code> to <code>Trigger</code> which stores different
     * subterms of <code>allTerm</code> with its according trigger
     */
    private final Map<JTerm, Trigger> termToTrigger = new LinkedHashMap<>();
    /** all universal variables of <code>allTerm</code> */
    private final ImmutableSet<QuantifiableVariable> uniQuantifiedVariables;
    /**
     * Replacement of the bound variables in <code>allTerm</code> with metavariables and constants
     */
    private final Substitution replacementWithMVs;

    private TriggersSet(JTerm allTerm, Services services) {
        this.allTerm = allTerm;
        replacementWithMVs =
            ReplacerOfQuanVariablesWithMetavariables.createSubstitutionForVars(allTerm, services);
        uniQuantifiedVariables = getAllUQS(allTerm);
        initTriggers(services);
    }

    static TriggersSet create(JTerm allTerm, Services services) {
        final Map<org.key_project.logic.Term, TriggersSet> triggerSetCache =
            services.getCaches().getTriggerSetCache();
        allTerm = TermLabelManager.removeIrrelevantLabels(allTerm, services);
        TriggersSet trs;

        synchronized (triggerSetCache) {
            trs = triggerSetCache.get(allTerm);
        }

        if (trs == null) {
            // add check whether it is in PCNF
            trs = new TriggersSet(allTerm, services);
            synchronized (triggerSetCache) {
                triggerSetCache.put(allTerm, trs);
            }
        }
        return trs;
    }

    /**
     * @param allterm
     * @return return all univesal variables of <code>allterm</code>
     */
    private ImmutableSet<QuantifiableVariable> getAllUQS(JTerm allterm) {
        final var op = allterm.op();
        if (op == Quantifier.ALL) {
            QuantifiableVariable v = allterm.varsBoundHere(0).get(0);
            return getAllUQS(allterm.sub(0)).add(v);
        }
        if (op == Quantifier.EX) {
            return getAllUQS(allterm.sub(0));
        }
        return DefaultImmutableSet.nil();
    }

    /**
     * initial all <code>Trigger</code>s by finding triggers in every clauses
     */
    private void initTriggers(Services services) {
        final QuantifiableVariable var = allTerm.varsBoundHere(0).get(0);
        final var it =
            TriggerUtils.iteratorByOperator(TriggerUtils.discardQuantifiers(allTerm), Junctor.AND);
        while (it.hasNext()) {
            final var clause = (JTerm) it.next();
            // a trigger should contain the first variable of allTerm
            if (clause.freeVars().contains(var)) {
                ClauseTrigger ct = new ClauseTrigger(clause);
                ct.createTriggers(services);
            }
        }
    }

    /**
     *
     * @param trigger a <code>Term</code>
     * @param qvs all universal variables of <code>trigger</code>
     * @param isUnify true if <code>trigger</code>contains existential variable
     * @param isElement true if the <code>Trigger</code> to be created is taken as a element of
     *        multi-trigger
     * @return a <code>Trigger</code> with <code>trigger</code> as its term
     */
    private Trigger createUniTrigger(JTerm trigger, ImmutableSet<QuantifiableVariable> qvs,
            boolean isUnify, boolean isElement) {
        Trigger t = termToTrigger.get(trigger);
        if (t == null) {
            t = new UniTrigger(trigger, qvs, isUnify, isElement, this);
            termToTrigger.put(trigger, t);
        }
        return t;
    }

    /**
     *
     * @param trs
     * @param clause a <code>Term</code> of clause form
     * @param qvs all universal varaibles of all <code>clause</code>
     * @return the MultTrigger for the given triggers
     */
    private Trigger createMultiTrigger(ImmutableSet<Trigger> trs, JTerm clause,
            ImmutableSet<QuantifiableVariable> qvs) {
        return new MultiTrigger(trs, qvs, clause);
    }

    /**
     * this class is used to find <code>Trigger</code>s in a clause. And it will try to find
     * triggers from every literals in this clause. Every substerm of literal that satify the
     * conditions:(1)it should not be a variable, (2) it doesn't contain propersitional connectives,
     * (3) it is not in loop, (4) it should contains all universal variables in the clause and the
     * first variable of <code>allTerm</code> (5) it doesn't contain subtrigger, will be selected as
     * an Uni-trigger. If a literal does not contain all universal variables in clause, a set of
     * subterms of this literal will be selected as Multi-trigger's elements which are actually
     * uni-triggers except that condition (2) will be changedand into that it contains all universal
     * variables in the literal in. Afterwards, a set of multi-triggers will be constructed by
     * combining thoes elements so that all variables in clause should be include by some of them.
     */
    private class ClauseTrigger {

        final JTerm clause;
        /** all unversal variables of <code>clause</code> */
        final ImmutableSet<QuantifiableVariable> selfUQVS;
        /**
         * elements which are uni-trigges and will be used to construct several multi-triggers for
         * <code>clause</code>
         */
        private ImmutableSet<Trigger> elementsOfMultiTrigger = DefaultImmutableSet.nil();

        public ClauseTrigger(JTerm clause) {
            this.clause = clause;
            selfUQVS = TriggerUtils.intersect(this.clause.freeVars(), uniQuantifiedVariables);

        }

        /**
         * Searching uni-triggers and elements of multi-triggers in every literal in this
         * <code>clause</code> and add those uni-triggers to the goal trigger set. At last construct
         * multi-triggers from those elements.
         */
        public void createTriggers(Services services) {
            final var it = TriggerUtils.iteratorByOperator(clause, Junctor.OR);
            while (it.hasNext()) {
                final JTerm oriTerm = (JTerm) it.next();
                for (JTerm term : expandIfThenElse(oriTerm, services)) {
                    JTerm t = term;
                    if (t.op() == Junctor.NOT) {
                        t = t.sub(0);
                    }
                    recAddTriggers(t, services);
                }
            }
            setMultiTriggers(elementsOfMultiTrigger.iterator());
        }

        /**
         * @param term one atom at the begining
         * @param services the Services
         * @return true if find any trigger from <code>term</code>
         */
        private boolean recAddTriggers(JTerm term, Services services) {
            if (!mightContainTriggers(term)) {
                return false;
            }

            final ImmutableSet<QuantifiableVariable> uniVarsInTerm =
                TriggerUtils.intersect(term.freeVars(), selfUQVS);

            boolean foundSubtriggers = false;
            for (int i = 0; i < term.arity(); i++) {
                final JTerm subTerm = term.sub(i);
                final boolean found = recAddTriggers(subTerm, services);

                if (found && uniVarsInTerm.subset(subTerm.freeVars())) {
                    foundSubtriggers = true;
                }
            }

            if (!foundSubtriggers) {
                addUniTrigger(term, services);
                return true;
            }

            return true;
        }

        private Set<JTerm> expandIfThenElse(JTerm t, TermServices services) {
            final Set<JTerm>[] possibleSubs = new Set[t.arity()];
            boolean changed = false;
            for (int i = 0; i != t.arity(); ++i) {
                final JTerm oriSub = t.sub(i);
                possibleSubs[i] = expandIfThenElse(oriSub, services);
                changed = changed || possibleSubs[i].size() != 1
                        || possibleSubs[i].iterator().next() != oriSub;
            }

            final Set<JTerm> res = new LinkedHashSet<>();
            if (t.op() == IfThenElse.IF_THEN_ELSE) {
                res.addAll(possibleSubs[1]);
                res.addAll(possibleSubs[2]);
            }

            if (!changed) {
                res.add(t);
                return res;
            }

            final JTerm[] chosenSubs = new JTerm[t.arity()];
            res.addAll(combineSubterms(t, possibleSubs, chosenSubs, t.boundVars(), 0, services));
            return res;
        }

        private Set<JTerm> combineSubterms(JTerm oriTerm, Set<JTerm>[] possibleSubs,
                JTerm[] chosenSubs,
                ImmutableArray<QuantifiableVariable> boundVars, int i,
                TermServices services) {
            final HashSet<JTerm> set = new LinkedHashSet<>();
            if (i >= possibleSubs.length) {
                final JTerm res = services.getTermFactory().createTerm(oriTerm.op(), chosenSubs,
                    boundVars, null);


                set.add(res);
                return set;
            }


            for (JTerm term : possibleSubs[i]) {
                chosenSubs[i] = term;
                set.addAll(
                    combineSubterms(oriTerm, possibleSubs, chosenSubs, boundVars, i + 1, services));
            }
            return set;
        }

        /**
         * Check whether a given term (or a subterm of the term) might be a trigger candidate
         */
        private boolean mightContainTriggers(JTerm term) {
            if (term.freeVars().isEmpty()) {
                return false;
            }
            final Operator op = term.op();
            if (op instanceof JModality || op instanceof UpdateApplication
                    || op instanceof QuantifiableVariable) {
                return false;
            }
            return UniTrigger.passedLoopTest(term, allTerm);
        }

        /**
         * Further criteria for triggers. This is just a HACK, there should be a more general
         * framework for characterising acceptable triggers
         */
        private boolean isAcceptableTrigger(JTerm term, Services services) {
            final Operator op = term.op();

            // we do not want to match on expressions a.<created>

            if (term.op() == services.getTypeConverter().getHeapLDT().getSelect(term.sort(),
                services)) {
                if (term.sub(2).op().name().toString()
                        .endsWith(ImplicitFieldAdder.IMPLICIT_CREATED)) {
                    return false;
                }
            }

            final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
            // matching on equations and inequalities does not seem to have any
            // positive effect for the time being
            return op != Equality.EQUALS && op != integerLDT.getLessOrEquals()
                    && op != integerLDT.getGreaterOrEquals();

            /*
             * if ( op == Op.EQUALS ) { // we do not want to match on equations t = null if (
             * term.sub ( 0 ).sort () == Sort.NULL || term.sub ( 1 ).sort () == Sort.NULL ) return
             * false; // we do not want to match on equations t = TRUE if ( "TRUE".equals ( term.sub
             * ( 0 ).op ().name ().toString () ) || "TRUE".equals ( term.sub ( 1 ).op ().name
             * ().toString () ) ) return false; }
             */
        }

        /**
         * add a uni-trigger to triggers set or add an element of multi-triggers for this clause
         */
        private void addUniTrigger(JTerm term, Services services) {
            if (!isAcceptableTrigger(term, services)) {
                return;
            }
            final boolean isUnify = !term.freeVars().subset(selfUQVS);
            final boolean isElement = !selfUQVS.subset(term.freeVars());
            final ImmutableSet<QuantifiableVariable> uniVarsInTerm =
                TriggerUtils.intersect(term.freeVars(), selfUQVS);
            Trigger t = createUniTrigger(term, uniVarsInTerm, isUnify, isElement);
            if (isElement) {
                elementsOfMultiTrigger = elementsOfMultiTrigger.add(t);
            } else {
                allTriggers = allTriggers.add(t);
            }
        }


        /**
         * find all possible combination of <code>ts</code>. Once a combination of elements contains
         * all variables of this clause, it will be used to construct the multi-trigger which will
         * be add to triggers set
         *
         * @param ts elements of multi-triggers at the beginning
         * @return a set of triggers
         */
        private Set<ImmutableSet<Trigger>> setMultiTriggers(Iterator<Trigger> ts) {
            Set<ImmutableSet<Trigger>> res = new LinkedHashSet<>();
            if (ts.hasNext()) {
                final Trigger trigger = ts.next();
                ImmutableSet<Trigger> tsi = DefaultImmutableSet.<Trigger>nil().add(trigger);
                res.add(tsi);
                Set<ImmutableSet<Trigger>> nextTriggers = setMultiTriggers(ts);

                res.addAll(nextTriggers);
                for (ImmutableSet<Trigger> nextTrigger : nextTriggers) {
                    ImmutableSet<Trigger> next = nextTrigger;
                    next = next.add(trigger);
                    if (addMultiTrigger(next)) {
                        continue;
                    }
                    res.add(next);
                }
            }
            return res;
        }

        /**
         * try to construct a multi-trigger by given <code>ts</code>
         *
         * @param trs a set of trigger
         * @return true if <code>trs</code> contains all universal varaibles of this clause, and add
         *         the contstructed multi-trigger to triggers set
         */
        private boolean addMultiTrigger(ImmutableSet<Trigger> trs) {
            ImmutableSet<QuantifiableVariable> mulqvs =
                DefaultImmutableSet.nil();
            for (Trigger tr : trs) {
                mulqvs =
                    mulqvs.union(((JTerm) tr.getTriggerTerm()).freeVars());
            }
            if (selfUQVS.subset(mulqvs)) {
                Trigger mt = createMultiTrigger(trs, clause, selfUQVS);
                allTriggers = allTriggers.add(mt);
                return true;
            }
            return false;
        }
    }

    public JTerm getQuantifiedFormula() {
        return allTerm;
    }

    public ImmutableSet<Trigger> getAllTriggers() {
        return allTriggers;
    }

    public Substitution getReplacementWithMVs() {
        return replacementWithMVs;
    }

    public ImmutableSet<QuantifiableVariable> getUniQuantifiedVariables() {
        return uniQuantifiedVariables;
    }
}

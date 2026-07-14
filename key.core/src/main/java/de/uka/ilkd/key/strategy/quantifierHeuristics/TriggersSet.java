/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.transformations.pipeline.PipelineConstants;
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
        uniQuantifiedVariables = collectUniversalVariables(allTerm);
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
    private ImmutableSet<QuantifiableVariable> collectUniversalVariables(JTerm allterm) {
        final var op = allterm.op();
        if (op == Quantifier.ALL) {
            QuantifiableVariable v = allterm.varsBoundHere(0).get(0);
            return collectUniversalVariables(allterm.sub(0)).add(v);
        }
        if (op == Quantifier.EX) {
            return collectUniversalVariables(allterm.sub(0));
        }
        return DefaultImmutableSet.nil();
    }

    /**
     * initial all <code>Trigger</code>s by finding triggers in every clauses
     */
    private void initTriggers(Services services) {
        final QuantifiableVariable firstVariable = allTerm.varsBoundHere(0).get(0);
        final var clauses =
            TriggerUtils.iteratorByOperator(TriggerUtils.discardQuantifiers(allTerm), Junctor.AND);
        while (clauses.hasNext()) {
            final var clause = (JTerm) clauses.next();
            // a trigger must contain the first variable of the quantified formula
            if (clause.freeVars().contains(firstVariable)) {
                ClauseTriggerFinder finder = new ClauseTriggerFinder(clause);
                finder.createTriggers(services);
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
    private Trigger createUniTrigger(JTerm trigger,
            ImmutableSet<QuantifiableVariable> universalVariables, boolean isUnify,
            boolean isElement) {
        Trigger cached = termToTrigger.get(trigger);
        if (cached == null) {
            cached = new UniTrigger(trigger, universalVariables, isUnify, isElement, this);
            termToTrigger.put(trigger, cached);
        }
        return cached;
    }

    /**
     *
     * @param trs
     * @param clause a <code>Term</code> of clause form
     * @param qvs all universal varaibles of all <code>clause</code>
     * @return the MultTrigger for the given triggers
     */
    private Trigger createMultiTrigger(ImmutableSet<Trigger> elements, JTerm clause,
            ImmutableSet<QuantifiableVariable> clauseVariables) {
        return new MultiTrigger(elements, clauseVariables, clause);
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
    private class ClauseTriggerFinder {

        final JTerm clause;
        /** all unversal variables of <code>clause</code> */
        final ImmutableSet<QuantifiableVariable> clauseVariables;
        /**
         * elements which are uni-trigges and will be used to construct several multi-triggers for
         * <code>clause</code>
         */
        private ImmutableSet<Trigger> elementsOfMultiTrigger = DefaultImmutableSet.nil();

        public ClauseTriggerFinder(JTerm clause) {
            this.clause = clause;
            clauseVariables =
                TriggerUtils.intersect(this.clause.freeVars(), uniQuantifiedVariables);

        }

        /**
         * Searching uni-triggers and elements of multi-triggers in every literal in this
         * <code>clause</code> and add those uni-triggers to the goal trigger set. At last construct
         * multi-triggers from those elements.
         */
        public void createTriggers(Services services) {
            final var literals = TriggerUtils.iteratorByOperator(clause, Junctor.OR);
            while (literals.hasNext()) {
                final JTerm literal = (JTerm) literals.next();
                for (JTerm term : expandIfThenElse(literal, services)) {
                    JTerm positive = term;
                    if (positive.op() == Junctor.NOT) {
                        positive = positive.sub(0);
                    }
                    addMaximalUniTriggers(positive, services);
                }
            }
            buildCoveringMultiTriggers(elementsOfMultiTrigger.iterator());
        }

        /**
         * @param term one atom at the begining
         * @param services the Services
         * @return true if find any trigger from <code>term</code>
         */
        private boolean addMaximalUniTriggers(JTerm term, Services services) {
            if (!mightContainTriggers(term)) {
                return false;
            }

            final ImmutableSet<QuantifiableVariable> uniVarsInTerm =
                TriggerUtils.intersect(term.freeVars(), clauseVariables);

            boolean foundSubtriggers = false;
            for (int i = 0; i < term.arity(); i++) {
                final JTerm subTerm = term.sub(i);
                final boolean found = addMaximalUniTriggers(subTerm, services);

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

        @SuppressWarnings("unchecked")
        private Set<JTerm> expandIfThenElse(JTerm term, TermServices services) {
            final Set<JTerm>[] possibleSubs = new Set[term.arity()];
            boolean changed = false;
            for (int i = 0; i != term.arity(); ++i) {
                final JTerm originalSub = term.sub(i);
                possibleSubs[i] = expandIfThenElse(originalSub, services);
                changed = changed || possibleSubs[i].size() != 1
                        || possibleSubs[i].iterator().next() != originalSub;
            }

            final Set<JTerm> expansions = new LinkedHashSet<>();
            if (term.op() == IfThenElse.IF_THEN_ELSE) {
                expansions.addAll(possibleSubs[1]);
                expansions.addAll(possibleSubs[2]);
            }

            if (!changed) {
                expansions.add(term);
                return expansions;
            }

            final JTerm[] chosenSubs = new JTerm[term.arity()];
            expansions.addAll(
                combineSubterms(term, possibleSubs, chosenSubs, term.boundVars(), 0, services));
            return expansions;
        }

        private Set<JTerm> combineSubterms(JTerm originalTerm, Set<JTerm>[] possibleSubs,
                JTerm[] chosenSubs, ImmutableArray<QuantifiableVariable> boundVars, int i,
                TermServices services) {
            final Set<JTerm> result = new LinkedHashSet<>();
            if (i >= possibleSubs.length) {
                final JTerm combined = services.getTermFactory().createTerm(originalTerm.op(),
                    chosenSubs, boundVars, null);
                result.add(combined);
                return result;
            }

            for (JTerm chosen : possibleSubs[i]) {
                chosenSubs[i] = chosen;
                result.addAll(combineSubterms(originalTerm, possibleSubs, chosenSubs, boundVars,
                    i + 1, services));
            }
            return result;
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

            // we do not want to match on expressions a.$created

            if (term.op() == services.getTypeConverter().getHeapLDT().getSelect(term.sort(),
                services)) {
                if (term.sub(2).op().name().toString()
                        .endsWith(PipelineConstants.IMPLICIT_CREATED)) {
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
            final boolean isUnify = !term.freeVars().subset(clauseVariables);
            final boolean isElement = !clauseVariables.subset(term.freeVars());
            final ImmutableSet<QuantifiableVariable> uniVarsInTerm =
                TriggerUtils.intersect(term.freeVars(), clauseVariables);
            Trigger trigger = createUniTrigger(term, uniVarsInTerm, isUnify, isElement);
            if (isElement) {
                elementsOfMultiTrigger = elementsOfMultiTrigger.add(trigger);
            } else {
                allTriggers = allTriggers.add(trigger);
            }
        }


        /**
         * Enumerate combinations of the multi-trigger elements and register each combination that
         * covers all clause variables as a multi-trigger (via {@link #tryAddCoveringMultiTrigger}).
         * A covering combination is not extended further, so only minimal covering sets are kept.
         *
         * @param remainingElements the elements still to be combined
         * @return the non-covering partial combinations (used internally for the recursion)
         */
        private Set<ImmutableSet<Trigger>> buildCoveringMultiTriggers(
                Iterator<Trigger> remainingElements) {
            Set<ImmutableSet<Trigger>> partialCombinations = new LinkedHashSet<>();
            if (remainingElements.hasNext()) {
                final Trigger element = remainingElements.next();
                ImmutableSet<Trigger> singleton = DefaultImmutableSet.<Trigger>nil().add(element);
                partialCombinations.add(singleton);
                Set<ImmutableSet<Trigger>> tailCombinations =
                    buildCoveringMultiTriggers(remainingElements);

                partialCombinations.addAll(tailCombinations);
                for (ImmutableSet<Trigger> tailCombination : tailCombinations) {
                    ImmutableSet<Trigger> combination = tailCombination.add(element);
                    // A covering combination becomes a multi-trigger and is not extended further;
                    // its supersets would be redundant.
                    if (tryAddCoveringMultiTrigger(combination)) {
                        continue;
                    }
                    partialCombinations.add(combination);
                }
            }
            return partialCombinations;
        }

        /**
         * If the given combination of elements together covers all universal variables of the
         * clause, build a multi-trigger from it, add it to the trigger set and return {@code true};
         * otherwise return {@code false}.
         *
         * @param combination a set of uni-trigger elements
         */
        private boolean tryAddCoveringMultiTrigger(ImmutableSet<Trigger> combination) {
            ImmutableSet<QuantifiableVariable> coveredVariables = DefaultImmutableSet.nil();
            for (Trigger element : combination) {
                coveredVariables =
                    coveredVariables.union(((JTerm) element.getTriggerTerm()).freeVars());
            }
            if (clauseVariables.subset(coveredVariables)) {
                Trigger multiTrigger = createMultiTrigger(combination, clause, clauseVariables);
                allTriggers = allTriggers.add(multiTrigger);
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

/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.op.*;

import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

/**
 * This class is used to select and store <code>Trigger</code>s for a quantified formula in Prenex
 * CNF(PCNF).
 */
public class TriggersSet {

    /**
     * Per-theory support consulted for rejecting unsuitable trigger material, providing derived
     * triggers, and (from {@link PredictCostProver}) deciding literals during cost prediction.
     * Support for a further theory is added by extending this list. The order is significant for
     * cost prediction: literals are decided by the first support that reaches a verdict, so
     * equality
     * is consulted before integer arithmetic, matching the original prover.
     */
    static final java.util.List<QuantifierTheorySupport> THEORY_SUPPORTS =
        java.util.List.of(new HeapArrayTheorySupport(), new EqualityTheorySupport(),
            new IntegerTheorySupport());

    /** Quantified formula of PCNF */
    private final JTerm allTerm;
    /**
     * The triggers collected while this set is built. A hash set answers the duplicate check in
     * constant time, whereas {@link ImmutableSet#add} scans the elements it already holds, which
     * costs quadratic time in the number of triggers a clause yields. Collection order is kept so
     * {@link #getAllTriggers()} can hand out exactly the set repeated adds would have produced.
     */
    private final LinkedHashSet<Trigger> collectedTriggers = new LinkedHashSet<>();

    /** Built from {@link #collectedTriggers} on first request. */
    private ImmutableSet<Trigger> allTriggers;
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
            boolean isElement, boolean matchByUnification) {
        Trigger cached = termToTrigger.get(trigger);
        if (cached == null) {
            cached = new UniTrigger(trigger, universalVariables, isUnify, isElement,
                matchByUnification, this);
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
            buildCoveringMultiTriggers();
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

            // a term becomes a trigger only if none of its subterms yielded one; a subterm
            // whose candidates were all rejected (not acceptable as triggers) does not count,
            // so the next enclosing meaningful term gets its chance
            if (!foundSubtriggers) {
                return addUniTrigger(term, services);
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
         * A trigger candidate is acceptable unless some theory's {@link QuantifierTheorySupport}
         * rejects it as coordinate or connective material.
         */
        private boolean isAcceptableTrigger(JTerm term, Services services) {
            for (final QuantifierTheorySupport support : THEORY_SUPPORTS) {
                if (support.rejectsAsTrigger(term, services)) {
                    return false;
                }
            }
            return true;
        }

        /**
         * add a uni-trigger to triggers set or add an element of multi-triggers for this clause,
         * together with the derived triggers each theory's {@link QuantifierTheorySupport} provides
         *
         * @return whether a trigger was registered for {@code term}
         */
        private boolean addUniTrigger(JTerm term, Services services) {
            if (!isAcceptableTrigger(term, services)) {
                return false;
            }
            registerUniTrigger(term, false);
            // A theory's generalisation is a different term, not a weaker one: it can match where
            // the original does not and fail to match where the original does. Both are therefore
            // registered, so an instantiation reachable through either one stays reachable.
            for (final QuantifierTheorySupport support : THEORY_SUPPORTS) {
                for (final JTerm derived : support.provideTriggers(term, clauseVariables,
                    services)) {
                    registerUniTrigger(derived, true);
                }
            }
            return true;
        }

        private void registerUniTrigger(JTerm term, boolean matchByUnification) {
            final boolean isUnify = !term.freeVars().subset(clauseVariables);
            final boolean isElement = !clauseVariables.subset(term.freeVars());
            final ImmutableSet<QuantifiableVariable> uniVarsInTerm =
                TriggerUtils.intersect(term.freeVars(), clauseVariables);
            Trigger trigger =
                createUniTrigger(term, uniVarsInTerm, isUnify, isElement, matchByUnification);
            if (isElement) {
                elementsOfMultiTrigger = elementsOfMultiTrigger.add(trigger);
            } else {
                collectedTriggers.add(trigger);
            }
        }


        /**
         * Registers a multi-trigger for every minimal set of elements that together cover the
         * clause's universal variables.
         *
         * A covering set is minimal when each member contributes a variable the other members do
         * not, so a minimal cover never has more members than the clause has variables. The search
         * looks for such covers directly: it takes a variable that is still uncovered, tries each
         * element covering it, and abandons a branch as soon as a member is left contributing
         * nothing (see {@link #keepOwnedVariables}). Building all combinations of the elements
         * instead and keeping the covering ones yields the same instantiations, but visits 2^n
         * combinations, which is out of reach once a clause offers a few dozen elements.
         */
        private void buildCoveringMultiTriggers() {
            final List<Trigger> elements = new ArrayList<>();
            final List<ImmutableSet<QuantifiableVariable>> coveredBy = new ArrayList<>();
            for (final Trigger element : elementsOfMultiTrigger) {
                elements.add(element);
                coveredBy.add(TriggerUtils
                        .intersect(((JTerm) element.getTriggerTerm()).freeVars(), clauseVariables));
            }
            coverRemainingVariables(clauseVariables, DefaultImmutableSet.nil(), new ArrayList<>(),
                elements, coveredBy);
        }

        /**
         * Extends {@code chosen} until it covers the clause variables, registering every complete
         * cover as a multi-trigger.
         *
         * @param uncovered the clause variables that no member of {@code chosen} covers yet
         * @param chosen the elements picked so far
         * @param ownedVariables for each element in {@code chosen}, the clause variables that
         *        element alone covers
         * @param elements the multi-trigger elements of the clause
         * @param coveredBy for each element, the clause variables that element covers
         */
        private void coverRemainingVariables(ImmutableSet<QuantifiableVariable> uncovered,
                ImmutableSet<Trigger> chosen,
                List<ImmutableSet<QuantifiableVariable>> ownedVariables, List<Trigger> elements,
                List<ImmutableSet<QuantifiableVariable>> coveredBy) {
            if (uncovered.isEmpty()) {
                tryAddCoveringMultiTrigger(chosen);
                return;
            }
            // Resolve one fixed variable per step: every member is then justified by the variable
            // it was picked for, so no branch grows a set that already covers the clause.
            final QuantifiableVariable target = uncovered.iterator().next();
            for (int i = 0, sz = elements.size(); i < sz; i++) {
                final Trigger element = elements.get(i);
                final ImmutableSet<QuantifiableVariable> covers = coveredBy.get(i);
                if (!covers.contains(target) || chosen.contains(element)) {
                    continue;
                }
                final List<ImmutableSet<QuantifiableVariable>> owned =
                    new ArrayList<>(ownedVariables.size() + 1);
                if (!keepOwnedVariables(ownedVariables, covers, owned)) {
                    continue;
                }
                ImmutableSet<QuantifiableVariable> remaining = uncovered;
                for (final QuantifiableVariable covered : covers) {
                    remaining = remaining.remove(covered);
                }
                owned.add(TriggerUtils.intersect(covers, uncovered));
                coverRemainingVariables(remaining, chosen.add(element), owned, elements, coveredBy);
            }
        }

        /**
         * Takes the variables a newly picked element covers away from the elements picked before
         * it. An element that is left owning nothing covers only variables the others already
         * cover, so the cover under construction would still cover the clause without it. Such a
         * cover is never built: a multi-trigger fires only when all of its elements match, so the
         * cover without the element fires whenever the one with it does, and yields the same
         * instantiations from fewer matches.
         *
         * @param ownedVariables for each element picked so far, the variables it alone covers
         * @param covers the clause variables the newly picked element covers
         * @param owned receives the reduced ownership of the elements picked so far
         * @return whether every element picked so far still owns a variable
         */
        private boolean keepOwnedVariables(List<ImmutableSet<QuantifiableVariable>> ownedVariables,
                ImmutableSet<QuantifiableVariable> covers,
                List<ImmutableSet<QuantifiableVariable>> owned) {
            for (final ImmutableSet<QuantifiableVariable> ownedByEarlier : ownedVariables) {
                ImmutableSet<QuantifiableVariable> left = ownedByEarlier;
                for (final QuantifiableVariable covered : covers) {
                    left = left.remove(covered);
                }
                if (left.isEmpty()) {
                    return false;
                }
                owned.add(left);
            }
            return true;
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
                collectedTriggers.add(multiTrigger);
                return true;
            }
            return false;
        }
    }

    public JTerm getQuantifiedFormula() {
        return allTerm;
    }

    public ImmutableSet<Trigger> getAllTriggers() {
        if (allTriggers == null) {
            // Adding to an immutable set prepends, so building it by repeated adds leaves the
            // triggers in the reverse of the order they were collected. Reverse here as well, so
            // the trigger order the strategy sees does not depend on how the set was assembled.
            allTriggers = DefaultImmutableSet
                    .fromImmutableList(ImmutableList.fromList(collectedTriggers).reverse());
        }
        return allTriggers;
    }

    public Substitution getReplacementWithMVs() {
        return replacementWithMVs;
    }

    public ImmutableSet<QuantifiableVariable> getUniQuantifiedVariables() {
        return uniQuantifiedVariables;
    }
}

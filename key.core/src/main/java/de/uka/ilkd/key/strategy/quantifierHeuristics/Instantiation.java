/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;

import org.key_project.util.collection.DefaultImmutableMap;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

class Instantiation {


    /** universally quantifiable variable bound in<code>allTerm</code> */
    private final QuantifiableVariable firstVar;

    private final Term matrix;

    /**
     * Literals occurring in the sequent at hand. This is used for branch prediction
     */
    private ImmutableSet<Term> assumedLiterals = DefaultImmutableSet.nil();

    /** HashMap from instance(<code>Term</code>) to cost <code>Long</code> */
    private final Map<Term, Long> instancesWithCosts = new LinkedHashMap<>();

    /** the <code>TriggersSet</code> of this <code>allTerm</code> */
    private final TriggersSet triggersSet;

    private Instantiation(Term allterm, Sequent seq, Services services) {
        firstVar = allterm.varsBoundHere(0).get(0);
        matrix = TriggerUtils.discardQuantifiers(allterm);
        /* Terms bound in every formula on <code>goal</code> */
        triggersSet = TriggersSet.create(allterm, services);
        assumedLiterals = initAssertLiterals(seq, services);
        addInstances(sequentToTerms(seq), services);
    }

    private static Term lastQuantifiedFormula = null;
    private static Sequent lastSequent = null;
    private static Instantiation lastResult = null;

    static Instantiation create(Term qf, Sequent seq, Services services) {
        synchronized (Instantiation.class) {
            if (qf == lastQuantifiedFormula && seq == lastSequent) {
                return lastResult;
            }
        }
        final Instantiation result = new Instantiation(qf, seq, services);
        synchronized (Instantiation.class) {
            lastQuantifiedFormula = qf;
            lastSequent = seq;
            lastResult = result;
        }
        return result;
    }

    private static ImmutableSet<Term> sequentToTerms(Sequent seq) {
        ImmutableList<Term> res = ImmutableSLList.nil();
        for (final SequentFormula cf : seq) {
            res = res.prepend(cf.formula());
        }
        return DefaultImmutableSet.fromImmutableList(res);
    }

    /**
     * @param terms on which trigger are doning matching search every <code>Substitution</code> s by
     *        matching <code>triggers</code> from <code>triggersSet</code> to <code>terms</code>
     *        compute their cost and store the pair of instance (Term) and cost(Long) in
     *        <code>instancesCostCache</code>
     */
    private void addInstances(ImmutableSet<Term> terms, Services services) {
        for (final Trigger t : triggersSet.getAllTriggers()) {
            for (final Substitution sub : t.getSubstitutionsFromTerms(terms, services)) {
                addInstance(sub, services);
            }
        }
        // if ( instancesWithCosts.isEmpty () )
        // ensure that there is always at least one instantiation
        // addArbitraryInstance ();
    }

    private void addArbitraryInstance(Services services) {
        ImmutableMap<QuantifiableVariable, Term> varMap =
            DefaultImmutableMap.nilMap();

        for (QuantifiableVariable v : triggersSet.getUniQuantifiedVariables()) {
            final Term inst = createArbitraryInstantiation(v, services);
            varMap = varMap.put(v, inst);
        }

        addInstance(new Substitution(varMap), services);
    }

    private Term createArbitraryInstantiation(QuantifiableVariable var, Services services) {
        return services.getTermBuilder().func(
            services.getJavaDLTheory().getCastSymbol(var.sort(), services),
            services.getTermBuilder().zero());
    }

    private void addInstance(Substitution sub, Services services) {
        final long cost =
            PredictCostProver.computerInstanceCost(sub, getMatrix(), assumedLiterals, services);
        if (cost != -1) {
            addInstance(sub, cost);
        }
    }

    /**
     * add instance of <code>var</code> in <code>sub</code> with <code>cost</code> to
     * <code>instancesCostCache</code> if this instance is exist, compare thire cost and store the
     * less one.
     *
     * @param sub
     * @param cost
     */
    private void addInstance(Substitution sub, long cost) {
        final Term inst = sub.getSubstitutedTerm(firstVar);
        final Long oldCost = instancesWithCosts.get(inst);
        if (oldCost == null || oldCost >= cost) {
            instancesWithCosts.put(inst, cost);
        }
    }

    /**
     * @param seq
     * @param services TODO
     * @return all literals in antesequent, and all negation of literal in succedent
     */
    private ImmutableSet<Term> initAssertLiterals(Sequent seq, TermServices services) {
        ImmutableList<Term> assertLits = ImmutableSLList.nil();
        for (final SequentFormula cf : seq.antecedent()) {
            final Term atom = cf.formula();
            final Operator op = atom.op();
            if (!(op == Quantifier.ALL || op == Quantifier.EX)) {
                assertLits = assertLits.prepend(atom);
            }
        }
        for (final SequentFormula cf : seq.succedent()) {
            final Term atom = cf.formula();
            final Operator op = atom.op();
            if (!(op == Quantifier.ALL || op == Quantifier.EX)) {
                assertLits = assertLits.prepend(services.getTermBuilder().not(atom));
            }
        }
        return DefaultImmutableSet.fromImmutableList(assertLits);
    }

    /**
     * Try to find the cost of an instance(inst) according its quantified formula and current goal.
     */
    static RuleAppCost computeCost(Term inst, Term form, Sequent seq, Services services) {
        return Instantiation.create(form, seq, services).computeCostHelp(inst);
    }

    private RuleAppCost computeCostHelp(Term inst) {
        Long cost = instancesWithCosts.get(inst);
        if (cost == null && (inst.op() instanceof SortDependingFunction
                && ((SortDependingFunction) inst.op()).getKind().equals(JavaDLTheory.CAST_NAME))) {
            cost = instancesWithCosts.get(inst.sub(0));
        }

        if (cost == null) {
            // if (triggersSet)
            return TopRuleAppCost.INSTANCE;
        }
        if (cost == -1) {
            return TopRuleAppCost.INSTANCE;
        }

        return NumberRuleAppCost.create(cost);
    }

    /** get all instances from instancesCostCache subsCache */
    ImmutableSet<Term> getSubstitution() {
        ImmutableSet<Term> res = DefaultImmutableSet.nil();
        for (final Term inst : instancesWithCosts.keySet()) {
            res = res.add(inst);
        }
        return res;
    }

    private Term getMatrix() {
        return matrix;
    }

}

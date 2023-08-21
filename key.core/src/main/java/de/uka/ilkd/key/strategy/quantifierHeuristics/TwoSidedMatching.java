/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;

import org.key_project.util.collection.DefaultImmutableMap;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSet;

/**
 * Matching triggers within another quantifier expression. Problems with the current implementation:
 *
 * * the usage of EqualityConstraint for unification implies that a variable is never instantiated
 * with non-rigid terms
 *
 * * it is unclear whether certain instantiations are lost due to too strict type checks in
 * EqualityConstraint
 */
class TwoSidedMatching {

    private final UniTrigger trigger;
    private final Term triggerWithMVs;
    private final Substitution targetSubstWithMVs;
    private final Substitution triggerSubstWithMVs;
    private final Term targetWithMVs;

    /**
     * creates an instance of a two sided matching
     *
     * @param trigger the UniTrigger
     * @param targetTerm the term to match
     * @param services the Services
     */
    TwoSidedMatching(UniTrigger trigger, Term targetTerm, Services services) {
        this.trigger = trigger;
        this.targetSubstWithMVs = ReplacerOfQuanVariablesWithMetavariables
                .createSubstitutionForVars(targetTerm, services);
        this.triggerSubstWithMVs = trigger.getTriggerSetThisBelongsTo().getReplacementWithMVs();

        if (targetSubstWithMVs.isGround()) {
            this.targetWithMVs =
                targetSubstWithMVs.apply(TriggerUtils.discardQuantifiers(targetTerm), services);
        } else {
            this.targetWithMVs = null;
        }
        if (triggerSubstWithMVs.isGround()) {
            this.triggerWithMVs = triggerSubstWithMVs.apply(trigger.getTriggerTerm(), services);
        } else {
            this.triggerWithMVs = null;
        }
    }

    /**
     * returns the found matchings
     *
     * @param services the Services
     * @return the found matchings
     */
    ImmutableSet<Substitution> getSubstitutions(Services services) {
        if (triggerWithMVs == null || targetWithMVs == null) {
            // non ground subs not supported yet
            return DefaultImmutableSet.nil();
        }
        return getAllSubstitutions(targetWithMVs, services);
    }

    private ImmutableSet<Substitution> getAllSubstitutions(Term target, Services services) {
        ImmutableSet<Substitution> allsubs = DefaultImmutableSet.nil();
        Substitution sub = match(triggerWithMVs, target, services);
        if (sub != null
                && (trigger.isElementOfMultitrigger() || sub.isTotalOn(trigger.getUniVariables())
                // sub.containFreevar(trigger.ts.allTerm.
                // varsBoundHere(0).getQuantifiableVariable(0))
                )) {
            allsubs = allsubs.add(sub);
        }
        final Operator op = target.op();
        if (!(op instanceof Modality || op instanceof UpdateApplication)) {
            for (int i = 0; i < target.arity(); i++) {
                allsubs = allsubs.union(getAllSubstitutions(target.sub(i), services));
            }
        }
        return allsubs;
    }

    /** find a substitution in a allterm by using unification */
    private Substitution match(Term triggerTerm, Term targetTerm, Services services) {
        final Constraint c = Constraint.BOTTOM.unify(targetTerm, triggerTerm, services);
        if (c.isSatisfiable()) {
            ImmutableMap<QuantifiableVariable, Term> sub =
                DefaultImmutableMap.nilMap();
            for (QuantifiableVariable quantifiableVariable : trigger.getUniVariables()) {
                QuantifiableVariable q = quantifiableVariable;
                Term mv = triggerSubstWithMVs.getSubstitutedTerm(q);
                Term t = c.getInstantiation((Metavariable) (mv.op()), services);
                if (t == null || t.op() instanceof Metavariable) {
                    return null;
                }
                if (isGround(t)) {
                    sub = sub.put(q, t);
                }
            }
            if (sub.size() > 0) {
                return new Substitution(sub);
            }
        }
        return null;
    }

    private boolean isGround(Term t) {
        return !triggerSubstWithMVs.termContainsValue(t)
                && !targetSubstWithMVs.termContainsValue(t);
    }
}

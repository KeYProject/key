/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.Iterator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableMapEntry;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

class MultiTrigger implements Trigger {

    private final ImmutableSet<Trigger> triggers;

    private final ImmutableSet<QuantifiableVariable> qvs;

    private final Term clause;

    MultiTrigger(ImmutableSet<Trigger> triggers, ImmutableSet<QuantifiableVariable> qvs,
            Term clause) {
        this.triggers = triggers;
        this.qvs = qvs;
        this.clause = clause;
    }

    @Override
    public ImmutableSet<Substitution> getSubstitutionsFromTerms(ImmutableSet<Term> targetTerms,
            Services services) {
        ImmutableList<Substitution> res = ImmutableSLList.nil();

        ImmutableSet<Substitution> mulsubs =
            setMultiSubstitution(triggers.iterator(), targetTerms, services);

        for (Substitution sub : mulsubs) {
            if (sub.isTotalOn(qvs)) {
                res = res.prepend(sub);
            }
        }

        return DefaultImmutableSet.fromImmutableList(res);
    }

    /** help function for getMultiSubstitution */
    private ImmutableSet<Substitution> setMultiSubstitution(Iterator<? extends Trigger> ts,
            ImmutableSet<Term> terms, Services services) {
        ImmutableList<Substitution> res = ImmutableSLList.nil();
        if (ts.hasNext()) {
            ImmutableSet<Substitution> subi = ts.next().getSubstitutionsFromTerms(terms, services);
            ImmutableSet<Substitution> nextSubs = setMultiSubstitution(ts, terms, services);
            if (nextSubs.isEmpty()) {
                return subi;
            } else if (subi.isEmpty()) {
                return nextSubs;
            }
            for (Substitution sub0 : nextSubs) {
                for (Substitution subiSub : subi) {
                    final Substitution sub1 = unifySubstitution(sub0, subiSub);
                    if (sub1 != null) {
                        res = res.prepend(sub1);
                    }
                }

            }
        }
        return DefaultImmutableSet.fromImmutableList(res);
    }

    /**
     * unify two substitution, if same variable are bound with same term return a new substitution
     * with all universal quantifiable variables in two substituition, otherwise return null
     */
    private Substitution unifySubstitution(Substitution sub0, Substitution sub1) {
        final ImmutableMap<QuantifiableVariable, Term> varMap1 = sub1.getVarMap();
        ImmutableMap<QuantifiableVariable, Term> resMap = varMap1;

        for (final ImmutableMapEntry<QuantifiableVariable, Term> en : sub0.getVarMap()) {
            QuantifiableVariable key = en.key();
            Term value = en.value();
            if (varMap1.containsKey(key)) {
                if (!(varMap1.get(key).equals(value))) {
                    return null;
                }
            }
            resMap = resMap.put(key, value);
        }
        return new Substitution(resMap);
    }

    @Override
    public boolean equals(Object arg0) {
        if (!(arg0 instanceof MultiTrigger)) {
            return false;
        }

        final MultiTrigger a = (MultiTrigger) arg0;
        return a.triggers.equals(triggers);
    }

    @Override
    public int hashCode() {
        return triggers.hashCode();
    }

    @Override
    public String toString() {
        return String.valueOf(triggers);
    }

    @Override
    public Term getTriggerTerm() {
        return clause;
    }

}

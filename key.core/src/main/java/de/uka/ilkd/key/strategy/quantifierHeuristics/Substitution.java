/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.Iterator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ClashFreeSubst;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;

import org.key_project.logic.Term;
import org.key_project.logic.TermCreationException;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSet;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This class decribes a substitution,which store a map(varMap) from quantifiable variable to a
 * term(instance).
 */
public class Substitution {
    private static final Logger LOGGER = LoggerFactory.getLogger(Substitution.class);

    private final ImmutableMap<QuantifiableVariable, Term> varMap;

    public Substitution(ImmutableMap<QuantifiableVariable, Term> map) {
        varMap = map;
    }

    public ImmutableMap<QuantifiableVariable, Term> getVarMap() {
        return varMap;
    }

    public Term getSubstitutedTerm(QuantifiableVariable var) {
        return varMap.get(var);
    }

    public boolean isTotalOn(ImmutableSet<? extends QuantifiableVariable> vars) {
        for (QuantifiableVariable var : vars) {
            if (!varMap.containsKey(var)) {
                return false;
            }
        }
        return true;
    }


    /**
     * @return true if every instance in the varMap does not contain variable.
     */
    public boolean isGround() {
        final Iterator<QuantifiableVariable> it = varMap.keyIterator();
        while (it.hasNext()) {
            final Term t = getSubstitutedTerm(it.next());
            if (!t.freeVars().isEmpty()) {
                LOGGER.debug("evil free vars in term: " + t);
                return false;
            }
        }
        return true;
    }


    public Term apply(Term t, Services services) {
        assert isGround() : "non-ground substitutions are not yet implemented: " + this;
        final Iterator<QuantifiableVariable> it = varMap.keyIterator();
        final TermBuilder tb = services.getTermBuilder();
        while (it.hasNext()) {
            final QuantifiableVariable var = it.next();
            final Sort quantifiedVarSort = var.sort();
            final Function quantifiedVarSortCast =
                services.getJavaDLTheory().getCastSymbol(quantifiedVarSort, services);
            Term instance = getSubstitutedTerm(var);
            if (!instance.sort().extendsTrans(quantifiedVarSort)) {
                instance = tb.func(quantifiedVarSortCast, (JTerm) instance);
            }
            t = applySubst(var, instance, t, tb);
        }
        return t;
    }

    private Term applySubst(QuantifiableVariable var, Term instance, Term t, TermBuilder tb) {
        final ClashFreeSubst subst =
            new ClashFreeSubst(var, (JTerm) instance, tb);
        return subst.apply((JTerm) t);
    }

    /**
     * Try to apply the substitution to a term, introducing casts if necessary (may never be the
     * case any more, XXX).
     * <p>
     * Fast path: all variables are substituted in a single traversal ({@link #applyGroundOnePass}).
     * This is sound because the substitution is ground (the instances contain no free variables, so
     * no capture can happen); shadowing of a substituted variable by a binder inside {@code t} is
     * respected. If a cast is required (the slow, possibly dead path), it falls back to the
     * per-variable substitution {@link #applyWithoutCastsPerVar}.
     */
    public Term applyWithoutCasts(Term t, Services services) {
        assert isGround() : "non-ground substitutions are not yet implemented: " + this;
        final TermBuilder tb = services.getTermBuilder();
        try {
            return applyGroundOnePass((JTerm) t, ImmutableList.nil(), tb);
        } catch (TermCreationException e) {
            return applyWithoutCastsPerVar(t, services);
        }
    }

    /**
     * Substitute every variable of {@link #varMap} in a single traversal of {@code t}. A variable
     * occurrence is replaced unless it is shadowed, i.e. re-bound by a binder above it (tracked in
     * {@code boundAbove}). Subterms in which no substituted variable occurs free are returned
     * unchanged.
     */
    private JTerm applyGroundOnePass(JTerm t, ImmutableList<QuantifiableVariable> boundAbove,
            TermBuilder tb) {
        // Variable leaves (the most common node) are handled directly, without the freeVars
        // bookkeeping of containsSubstVar.
        if (t.op() instanceof QuantifiableVariable qv) {
            final Term inst = varMap.get(qv);
            return inst != null && !boundAbove.contains(qv) ? (JTerm) inst : t;
        }
        if (!containsSubstVar(t)) {
            return t;
        }
        final int arity = t.arity();
        final JTerm[] newSubs = new JTerm[arity];
        boolean changed = false;
        for (int i = 0; i < arity; i++) {
            final JTerm sub = t.sub(i);
            ImmutableList<QuantifiableVariable> below = boundAbove;
            final var boundHere = t.varsBoundHere(i);
            for (int j = 0; j < boundHere.size(); j++) {
                below = below.prepend(boundHere.get(j));
            }
            newSubs[i] = applyGroundOnePass(sub, below, tb);
            if (newSubs[i] != sub) {
                changed = true;
            }
        }
        if (!changed) {
            return t;
        }
        return tb.tf().createTerm(t.op(), newSubs, t.boundVars(), t.getLabels());
    }

    /** Whether any variable of {@link #varMap} occurs free in {@code t}. */
    private boolean containsSubstVar(JTerm t) {
        final ImmutableSet<QuantifiableVariable> free = t.freeVars();
        if (free.isEmpty()) {
            return false;
        }
        final Iterator<QuantifiableVariable> it = varMap.keyIterator();
        while (it.hasNext()) {
            if (free.contains(it.next())) {
                return true;
            }
        }
        return false;
    }

    /** Per-variable substitution (one {@link ClashFreeSubst} pass per variable), with casts. */
    private Term applyWithoutCastsPerVar(Term t, Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final Iterator<QuantifiableVariable> it = varMap.keyIterator();
        while (it.hasNext()) {
            final QuantifiableVariable var = it.next();
            Term instance = getSubstitutedTerm(var);
            try {
                t = applySubst(var, instance, t, tb);
            } catch (TermCreationException e) {
                final Sort quantifiedVarSort = var.sort();
                if (!instance.sort().extendsTrans(quantifiedVarSort)) {
                    final Function quantifiedVarSortCast =
                        services.getJavaDLTheory().getCastSymbol(quantifiedVarSort, services);
                    instance =
                        tb.func(quantifiedVarSortCast, (JTerm) instance);
                    t = applySubst(var, instance, t, tb);
                } else {
                    throw e;
                }
            }
        }
        return t;
    }

    public boolean equals(Object arg0) {
        if (!(arg0 instanceof Substitution s)) {
            return false;
        }
        return varMap.equals(s.varMap);
    }

    public int hashCode() {
        return varMap.hashCode();
    }

    public String toString() {
        return String.valueOf(varMap);
    }

    public boolean termContainsValue(Term term) {
        Iterator<Term> it = varMap.valueIterator();
        while (it.hasNext()) {
            if (recOccurCheck(it.next(), term)) {
                return true;
            }
        }
        return false;
    }

    /**
     * check whether term "sub" is in term "term"
     */
    private boolean recOccurCheck(Term sub, Term term) {
        if (sub.equals(term)) {
            return true;
        }
        for (int i = 0; i < term.arity(); i++) {
            if (recOccurCheck(sub, term.sub(i))) {
                return true;
            }
        }
        return false;
    }
}

/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Equality;

import org.key_project.util.collection.ImmutableSet;

/**
 * Equality reasoning over the ground equalities assumed on a sequent, used by the quantifier
 * instantiation cost prediction. The two sides of every assumed equality are merged into a class,
 * and a term is rewritten to the representatives of its subterms, so that a clause literal already
 * satisfied by those equalities becomes syntactically equal to an assumed literal. The instance
 * then predicts as non-contributing and is not proposed as a useful step.
 *
 * Each merge is oriented the way the equality is written on the sequent: occurrences of the left
 * side rewrite to the right side. The proof search normalises sequent equalities by the rules of
 * the owning theory, so this direction is the theory-established one. A
 * {@link QuantifierTheorySupport} can veto a rewrite that would disturb the normal forms its
 * decisions depend on ({@link QuantifierTheorySupport#allowsEqualityRewrite}); then the opposite
 * direction is tried, and a doubly vetoed equality is left out of the congruence.
 *
 * One congruence is built per sequent in {@link Instantiation} and shared across the cost
 * predictions of all candidate instantiations of the quantified formula, so the union-find is
 * built once rather than once per candidate.
 */
final class Congruence {

    /** Union-find parent map over the terms merged by the assumed equalities. */
    private final Map<JTerm, JTerm> parent = new HashMap<>();

    /** The (cached) factory used to rebuild normalised terms. */
    private final TermFactory tf;

    /** Access to the theory operators, passed to the theory supports on each veto check. */
    private final Services services;

    /**
     * @param assumedLiterals the literals assumed true on the sequent
     * @param services access to the term factory and the theory operators
     */
    Congruence(ImmutableSet<JTerm> assumedLiterals, Services services) {
        this.services = services;
        this.tf = services.getTermFactory();
        for (final JTerm lit : assumedLiterals) {
            if (lit.op() == Equality.EQUALS) {
                union(lit.sub(0), lit.sub(1));
            }
        }
    }

    /** Results of {@link #normalize}; this object is per sequent and thread-confined. */
    private final Map<JTerm, JTerm> normalized = new HashMap<>();

    /** Whether the sequent asserts no equality; then {@link #normalize} is the identity. */
    boolean isTrivial() {
        return parent.isEmpty();
    }

    /** The representative of {@code t}'s class, or {@code t} itself if it is in no class. */
    private JTerm find(JTerm t) {
        // Iterative with a second compression pass: the merge direction is dictated by the
        // sequent, so ranks cannot bound the chains, and a recursive walk would grow the stack
        // with the chain length.
        JTerm root = t;
        JTerm p;
        while ((p = parent.get(root)) != null) {
            root = p;
        }
        JTerm walk = t;
        while ((p = parent.get(walk)) != null && p != root) {
            parent.put(walk, root);
            walk = p;
        }
        return root;
    }

    /**
     * Merges the classes of the two sides of an assumed equality {@code a = b}, preferring the
     * sequent's own orientation: the representative of {@code a}'s class points to the
     * representative of {@code b}'s class, so occurrences of the left side rewrite to the right
     * side. A direction that is ill sorted or vetoed by a theory support is not installed; then
     * the flipped direction is tried, and if that is rejected too the equality does not take part
     * in the congruence.
     */
    private void union(JTerm a, JTerm b) {
        final JTerm ra = find(a);
        final JTerm rb = find(b);
        if (ra.equals(rb)) {
            return;
        }
        if (allowed(ra, rb)) {
            parent.put(ra, rb);
        } else if (allowed(rb, ra)) {
            parent.put(rb, ra);
        }
    }

    /**
     * Whether occurrences of {@code from} may be rewritten to {@code to}.
     *
     * The representative's sort must equal or specialise the rewritten side's sort: every operator
     * position accepting a term of {@code from}'s sort then accepts the representative, so the
     * rebuild in {@link #normalize} stays well sorted. A widening direction is ill sorted: a
     * contract equality {@code cast<[int[]]>(dest) = dest} read left to right would put the
     * {@code Object}-sorted variable into positions requiring {@code int[]}. The sort condition
     * holds transitively along the parent links, since every link narrows the sort. On top of the
     * sort condition every theory support must permit the rewrite.
     *
     * @param from the class representative that would point to {@code to}
     * @param to the term that would become the representative of the merged class
     * @return whether the rewrite is well sorted and no theory support vetoes it
     */
    private boolean allowed(JTerm from, JTerm to) {
        if (to.sort() != from.sort() && !to.sort().extendsTrans(from.sort())) {
            return false;
        }
        for (final QuantifierTheorySupport support : TriggersSet.THEORY_SUPPORTS) {
            if (!support.allowsEqualityRewrite(from, to, services)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Rewrites {@code t} bottom-up, replacing each subterm by its class representative. Quantified
     * subterms are left untouched.
     *
     * @param t a term to normalise
     * @return the congruence-normal form of {@code t}
     */
    JTerm normalize(JTerm t) {
        if (parent.isEmpty() || !t.boundVars().isEmpty()) {
            return t;
        }
        // Shared subterms are re-normalized once per occurrence otherwise, and the literals of
        // one congruence are normalized again for every candidate instance sharing it.
        final JTerm memo = normalized.get(t);
        if (memo != null) {
            return memo;
        }
        final JTerm result = normalizeUncached(t);
        normalized.put(t, result);
        return result;
    }

    private JTerm normalizeUncached(JTerm t) {
        if (t.arity() == 0) {
            return find(t);
        }
        final JTerm[] subs = new JTerm[t.arity()];
        boolean changed = false;
        for (int i = 0; i < t.arity(); i++) {
            subs[i] = normalize(t.sub(i));
            if (subs[i] != t.sub(i)) {
                changed = true;
            }
        }
        if (!changed) {
            return find(t);
        }
        try {
            return find(tf.createTerm(t.op(), subs));
        } catch (org.key_project.logic.TermCreationException e) {
            // the orientation keeps rewrites sort-compatible, but an operator with a stricter
            // requirement can still reject the rebuilt term; this is only a heuristic, so give
            // the term up unnormalised rather than fail the proof search
            return t;
        }
    }
}

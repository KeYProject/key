/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.sort.SortImpl;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.logic.sort.Sort;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Property test for
 * {@link LexPathOrdering#compare(org.key_project.logic.Term, org.key_project.logic.Term)}.
 * The ordering is used pairwise to orient rewriting (a rule fires only when its left side is
 * strictly greater than its right side), so soundness of the arithmetic normalisation relies on
 * the strict part being a strict partial order: irreflexive, antisymmetric and transitive. If
 * antisymmetry fails, two terms could each rewrite to the other (a normalisation loop); if
 * transitivity fails, the ordering is not well founded. The order is only a partial order -- it
 * returns 0 both for equal and for incomparable terms -- so equivalence (compare == 0) is not
 * expected to be transitive and is not checked here.
 */
public class LexPathOrderingPropertyTest {

    private static JTerm t(TermFactory tf, Function f, JTerm... subs) {
        return tf.createTerm(f, subs);
    }

    /**
     * Probes the one antisymmetry hazard the curated-signature test above cannot reach: the
     * symbol precedence in {@link LexPathOrdering} ties only for equal-name symbols, so a signature
     * of distinct-named symbols is a total precedence and never exercises the {@code compareHelp2}
     * else-branch that is taken when the operator comparison is a tie and the lexicographic subterm
     * comparison is inconclusive. Here we deliberately introduce DISTINCT operator objects that
     * SHARE a name (a genuinely partial precedence layer), plus commutation swaps, and assert the
     * strict part stays antisymmetric -- a failure would be two terms each orienting below the
     * other, i.e. a rewrite loop.
     */
    @Test
    void sameNamedDistinctOpsDoNotBreakAntisymmetry() {
        final var services = de.uka.ilkd.key.rule.TacletForTests.services();
        final TermFactory tf = services.getTermFactory();
        final Sort s = new SortImpl(new Name("S"));

        // distinct operator objects sharing a name -> a precedence tie for non-identical ops
        final Function p1 = new JFunction(new Name("p"), s, s, s);
        final Function p2 = new JFunction(new Name("p"), s, s, s);
        final Function q1 = new JFunction(new Name("q"), s, s);
        final Function q2 = new JFunction(new Name("q"), s, s);
        final Function k1 = new JFunction(new Name("k"), s);
        final Function k2 = new JFunction(new Name("k"), s);
        final Function a = new JFunction(new Name("a"), s);
        final Function b = new JFunction(new Name("b"), s);
        final Function g = new JFunction(new Name("g"), s, s, s);

        final JTerm ta = t(tf, a), tb = t(tf, b);
        final List<JTerm> terms = new ArrayList<>();
        terms.add(t(tf, k1)); // constant named k
        terms.add(t(tf, k2));
        for (JTerm x : new JTerm[] { ta, tb }) {
            terms.add(t(tf, q1, x));
            terms.add(t(tf, q2, x));
            // commutation swaps under same-named binaries
            terms.add(t(tf, p1, x, x));
            terms.add(t(tf, p2, x, x));
        }
        terms.add(t(tf, p1, ta, tb));
        terms.add(t(tf, p2, tb, ta));
        terms.add(t(tf, g, t(tf, p1, ta, tb), t(tf, p2, tb, ta)));
        terms.add(t(tf, g, t(tf, p2, tb, ta), t(tf, p1, ta, tb)));
        terms.add(t(tf, p1, t(tf, q1, ta), t(tf, q2, ta)));
        terms.add(t(tf, p1, t(tf, q2, ta), t(tf, q1, ta)));

        final LexPathOrdering ord = new LexPathOrdering();
        final int n = terms.size();
        for (JTerm x : terms) {
            assertEquals(0, ord.compare(x, x), "compare(t,t) must be 0 for " + x);
        }
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                final int cij = Integer.signum(ord.compare(terms.get(i), terms.get(j)));
                final int cji = Integer.signum(ord.compare(terms.get(j), terms.get(i)));
                assertEquals(cij, -cji, "antisymmetry (rewrite-loop) violated for ["
                    + terms.get(i) + "] vs [" + terms.get(j) + "]");
            }
        }
        // transitivity of the strict part over the same-named signature
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                if (ord.compare(terms.get(i), terms.get(j)) >= 0) {
                    continue;
                }
                for (int m = 0; m < n; m++) {
                    if (ord.compare(terms.get(j), terms.get(m)) < 0) {
                        assertTrue(ord.compare(terms.get(i), terms.get(m)) < 0,
                            "transitivity violated: " + terms.get(i) + " < " + terms.get(j) + " < "
                                + terms.get(m));
                    }
                }
            }
        }
    }

    @Test
    void strictPartIsStrictPartialOrder() {
        final var services = de.uka.ilkd.key.rule.TacletForTests.services();
        final TermFactory tf = services.getTermFactory();

        final Sort s = new SortImpl(new Name("S"));
        // constants a, b, c; a unary f; two binaries g, h -- enough operator variety to exercise
        // the symbol precedence, the lexicographic subterm comparison and the subterm-dominance
        // checks of the LPO.
        final Function a = new JFunction(new Name("a"), s);
        final Function b = new JFunction(new Name("b"), s);
        final Function c = new JFunction(new Name("c"), s);
        final Function f = new JFunction(new Name("f"), s, s);
        final Function g = new JFunction(new Name("g"), s, s, s);
        final Function h = new JFunction(new Name("h"), s, s, s);

        final List<JTerm> base = new ArrayList<>();
        base.add(t(tf, a));
        base.add(t(tf, b));
        base.add(t(tf, c));

        final List<JTerm> terms = new ArrayList<>(base);
        // depth 1
        for (JTerm x : base) {
            terms.add(t(tf, f, x));
        }
        // depth 2 combinations over the two binaries and the unary
        for (JTerm x : base) {
            for (JTerm y : base) {
                terms.add(t(tf, g, x, y));
                terms.add(t(tf, h, x, y));
                terms.add(t(tf, f, t(tf, f, x)));
            }
        }
        // a few deeper, mixed nestings
        for (JTerm x : base) {
            terms.add(t(tf, g, t(tf, f, x), x));
            terms.add(t(tf, h, x, t(tf, g, x, x)));
            terms.add(t(tf, g, t(tf, g, x, x), t(tf, h, x, x)));
        }

        final LexPathOrdering ord = new LexPathOrdering();
        final int n = terms.size();

        // reflexive tie: compare(t, t) == 0
        for (JTerm x : terms) {
            assertEquals(0, ord.compare(x, x), "compare(t,t) must be 0 for " + x);
        }

        // antisymmetry: sign(compare(a,b)) == -sign(compare(b,a))
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                final int cij = Integer.signum(ord.compare(terms.get(i), terms.get(j)));
                final int cji = Integer.signum(ord.compare(terms.get(j), terms.get(i)));
                assertEquals(cij, -cji,
                    "antisymmetry violated for [" + terms.get(i) + "] vs [" + terms.get(j) + "]");
            }
        }

        // transitivity of the strict part: a<b and b<c imply a<c
        int strictTriplesChecked = 0;
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                if (ord.compare(terms.get(i), terms.get(j)) >= 0) {
                    continue;
                }
                for (int k = 0; k < n; k++) {
                    if (ord.compare(terms.get(j), terms.get(k)) < 0) {
                        strictTriplesChecked++;
                        assertTrue(ord.compare(terms.get(i), terms.get(k)) < 0,
                            "transitivity violated: [" + terms.get(i) + "] < [" + terms.get(j)
                                + "] < [" + terms.get(k) + "] but not [" + terms.get(i) + "] < ["
                                + terms.get(k) + "]");
                    }
                }
            }
        }
        assertTrue(strictTriplesChecked > 0, "no strict chains found, test set too flat");
    }
}

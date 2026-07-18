/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.sort.SortImpl;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.logic.sort.Sort;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Property test for {@code RuleAppContainer.compareByName}, the structural term comparison that is
 * the content key of the rule-application queue's tie-break. That queue is a leftist heap which
 * merges by pairwise comparisons, so the comparator must be a strict weak ordering: irreflexive,
 * antisymmetric, and both the strict part and the equivalence (compare == 0) transitive. On terms
 * without bound variables, program blocks or labels -- the comparator's documented blind spots --
 * it is meant to be a strict total order, so compare == 0 must coincide with structural equality;
 * this test builds exactly such terms and checks all four properties exhaustively.
 */
public class TieBreakComparatorPropertyTest {

    private static Method compareByName;

    private static int cmp(Term a, Term b) {
        try {
            if (compareByName == null) {
                compareByName = RuleAppContainer.class.getDeclaredMethod("compareByName",
                    Term.class, Term.class);
                compareByName.setAccessible(true);
            }
            return (int) compareByName.invoke(null, a, b);
        } catch (ReflectiveOperationException e) {
            throw new RuntimeException(e);
        }
    }

    private static JTerm t(TermFactory tf, Function f, JTerm... subs) {
        return tf.createTerm(f, subs);
    }

    @Test
    void compareByNameIsStrictTotalOrderOnLabelFreeTerms() {
        final var services = de.uka.ilkd.key.rule.TacletForTests.services();
        final TermFactory tf = services.getTermFactory();

        final Sort s = new SortImpl(new Name("S"));
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
        for (JTerm x : base) {
            terms.add(t(tf, f, x));
            for (JTerm y : base) {
                terms.add(t(tf, g, x, y));
                terms.add(t(tf, h, x, y));
                terms.add(t(tf, f, t(tf, f, x)));
                terms.add(t(tf, g, t(tf, f, x), y));
                terms.add(t(tf, h, x, t(tf, g, x, y)));
            }
        }
        final int n = terms.size();

        // reflexive tie: an element compares equal to itself
        for (JTerm x : terms) {
            assertEquals(0, cmp(x, x), "compare(t,t) must be 0");
        }
        // antisymmetry
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                assertEquals(Integer.signum(cmp(terms.get(i), terms.get(j))),
                    -Integer.signum(cmp(terms.get(j), terms.get(i))),
                    "antisymmetry violated for [" + terms.get(i) + "] vs [" + terms.get(j) + "]");
            }
        }
        // totality on label/binder/program-free terms: compare == 0 only for equal terms
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                final boolean tie = cmp(terms.get(i), terms.get(j)) == 0;
                final boolean equal = terms.get(i).equals(terms.get(j));
                assertEquals(equal, tie, "compare==0 must coincide with equality: ["
                    + terms.get(i) + "] vs [" + terms.get(j) + "]");
            }
        }
        // transitivity of the strict part
        int triples = 0;
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                if (cmp(terms.get(i), terms.get(j)) >= 0) {
                    continue;
                }
                for (int k = 0; k < n; k++) {
                    if (cmp(terms.get(j), terms.get(k)) < 0) {
                        triples++;
                        assertTrue(cmp(terms.get(i), terms.get(k)) < 0,
                            "transitivity violated: " + terms.get(i) + " < " + terms.get(j) + " < "
                                + terms.get(k));
                    }
                }
            }
        }
        assertTrue(triples > 0, "test set too flat");
    }
}

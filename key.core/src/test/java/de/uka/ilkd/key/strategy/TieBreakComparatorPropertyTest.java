/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.sort.SortImpl;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

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

    private static int cmp(Term a, Term b) {
        return RuleAppContainer.compareByName(a, b);
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

    /**
     * The invariant the production comparator rests on: {@code compareFormulasByName} tries the
     * cached name hash first and walks only on a hash tie, which is a total order exactly when a
     * walk tie implies a hash tie. Checked over structurally equal terms built as distinct
     * objects, so the identity shortcut cannot hide a violation.
     */
    @Test
    void walkTieImpliesNameHashTie() {
        final var services = de.uka.ilkd.key.rule.TacletForTests.services();
        final TermFactory tf = services.getTermFactory();
        final List<JTerm> terms = generatedTerms(tf);
        final List<JTerm> copies = generatedTerms(tf);
        int ties = 0;
        for (int i = 0; i < terms.size(); i++) {
            for (int j = 0; j < terms.size(); j++) {
                final Term a = terms.get(i);
                final Term b = copies.get(j);
                if (cmp(a, b) == 0) {
                    ties++;
                    assertEquals(a.nameHash(), b.nameHash(),
                        "walk tie without hash tie for [" + a + "] vs [" + b + "]");
                }
            }
        }
        assertTrue(ties >= terms.size(), "expected at least the diagonal ties");
    }

    /**
     * The production path {@code compareFormulasByName} must order exactly like the plain walk:
     * the hash is a discriminator for speed, never for a different order. A tie means a walk
     * tie, and where the hashes disagree the walk of that pair is what loses, so only the sign
     * consistency on hash ties can be asserted; totality and antisymmetry hold over the set.
     */
    @Test
    void formulaComparatorAgreesWithTheWalk() {
        final var services = de.uka.ilkd.key.rule.TacletForTests.services();
        final TermFactory tf = services.getTermFactory();
        final List<JTerm> terms = generatedTerms(tf);
        final List<JTerm> copies = generatedTerms(tf);
        for (int i = 0; i < terms.size(); i++) {
            for (int j = 0; j < terms.size(); j++) {
                final Term a = terms.get(i);
                final Term b = copies.get(j);
                final int full = RuleAppContainer.compareFormulasByName(a, b);
                final int back = RuleAppContainer.compareFormulasByName(b, a);
                assertEquals(Integer.signum(full), -Integer.signum(back),
                    "antisymmetry violated for [" + a + "] vs [" + b + "]");
                if (full == 0) {
                    assertEquals(0, cmp(a, b),
                        "formula comparator tie without walk tie for [" + a + "] vs [" + b + "]");
                }
                if (a.nameHash() == b.nameHash()) {
                    assertEquals(Integer.signum(cmp(a, b)), Integer.signum(full),
                        "hash-tied pair ordered differently than the walk: [" + a + "] vs ["
                            + b + "]");
                }
            }
        }
    }

    /**
     * Term labels are invisible to the ordering: a labeled variant shares the name hash and the
     * label-agnostic hash of the plain term and compares as a tie, although the two terms are
     * not equal.
     */
    @Test
    void orderingHashesIgnoreLabels() {
        final var services = de.uka.ilkd.key.rule.TacletForTests.services();
        final TermFactory tf = services.getTermFactory();
        final Sort s = new SortImpl(new Name("S"));
        final Function a = new JFunction(new Name("a"), s);
        final Function f = new JFunction(new Name("f"), s, s);
        final JTerm plain = t(tf, f, t(tf, a));
        final JTerm labeled = tf.createTerm(f, new JTerm[] { t(tf, a) },
            new ImmutableArray<TermLabel>(ParameterlessTermLabel.ANON_HEAP_LABEL));

        assertTrue(!plain.equals(labeled), "the label must matter for equality");
        assertEquals(plain.nameHash(), labeled.nameHash(), "nameHash must ignore labels");
        assertEquals(plain.labelAgnosticHash(), labeled.labelAgnosticHash(),
            "labelAgnosticHash must ignore labels");
        assertEquals(0, cmp(plain, labeled), "the walk must ignore labels");
        assertEquals(0, RuleAppContainer.compareFormulasByName(plain, labeled),
            "the production comparator must ignore labels");
    }

    /** The generated term set of the total-order test, built fresh so instances are distinct. */
    private static List<JTerm> generatedTerms(TermFactory tf) {
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
        return terms;
    }
}

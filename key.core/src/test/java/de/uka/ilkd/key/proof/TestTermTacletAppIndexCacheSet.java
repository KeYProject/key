/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import java.util.HashMap;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests that the state automaton of {@link TermTacletAppIndexCacheSet} tracks the position
 * polarity: rewrite taclets can be restricted to antecedent/succedent polarity
 * ({@link de.uka.ilkd.key.rule.RewriteTaclet#checkPrefix}), so positions of different polarity
 * index different taclet apps and must never share cache entries. (Sharing them made the cached
 * app sets depend on which occurrence of a term was indexed first — across all goals of the proof
 * — and thereby made proof search depend on the goal scheduling order.)
 */
public class TestTermTacletAppIndexCacheSet {

    private static JTerm and;
    private static JTerm or;
    private static JTerm not;
    private static JTerm imp;
    private static JTerm eqv;

    @BeforeAll
    static void setUp() {
        final Services services = HelperClassForTests.createServices();
        // build the junctor terms with the raw term factory -- the TermBuilder would simplify
        // terms over the constant subterm away (and(tt, tt) == tt)
        final TermFactory tf = services.getTermFactory();
        final JTerm tt = services.getTermBuilder().tt();
        and = tf.createTerm(Junctor.AND, tt, tt);
        or = tf.createTerm(Junctor.OR, tt, tt);
        not = tf.createTerm(Junctor.NOT, tt);
        imp = tf.createTerm(Junctor.IMP, tt, tt);
        eqv = tf.createTerm(Equality.EQV, tt, tt); // an equivalence zeroes the polarity
    }

    private static TermTacletAppIndexCacheSet newCacheSet() {
        return new TermTacletAppIndexCacheSet(new HashMap<>());
    }

    @Test
    public void testTopLevelCachesAreSeparatedBySide() {
        final TermTacletAppIndexCacheSet cs = newCacheSet();
        assertNotSame(cs.getAntecCache(), cs.getSuccCache(),
            "top-level antecedent and succedent positions index different taclets");
    }

    @Test
    public void testPolarityIsKeptBelowJunctors() {
        final TermTacletAppIndexCacheSet cs = newCacheSet();
        // polarity-preserving descents from opposite sides must not meet
        assertNotSame(cs.getAntecCache().descend(and, 0), cs.getSuccCache().descend(and, 0),
            "same term below a conjunction has polarity -1 in the antecedent "
                + "but +1 in the succedent");
        assertNotSame(cs.getAntecCache().descend(imp, 1), cs.getSuccCache().descend(imp, 1),
            "the implication conclusion keeps the polarity of its side");
        // ... while equal polarities reached along different paths share the cache
        assertSame(cs.getAntecCache().descend(and, 0), cs.getAntecCache().descend(or, 1),
            "conjunction and disjunction both keep polarity");
    }

    @Test
    public void testPolarityFlipsAtNegationAndImplicationPremiss() {
        final TermTacletAppIndexCacheSet cs = newCacheSet();
        // antecedent (-1) flipped once == succedent (+1) kept
        assertSame(cs.getAntecCache().descend(not, 0), cs.getSuccCache().descend(and, 0),
            "negation flips the polarity");
        assertSame(cs.getAntecCache().descend(imp, 0), cs.getSuccCache().descend(imp, 1),
            "the implication premiss flips, the conclusion keeps the polarity");
        // double flip is the identity
        assertSame(
            cs.getAntecCache().descend(not, 0).descend(not, 0),
            cs.getAntecCache().descend(and, 0),
            "two negations restore the polarity");
        // flipped vs kept on the same side differ
        assertNotSame(cs.getAntecCache().descend(not, 0), cs.getAntecCache().descend(and, 0),
            "a flipped position must not share entries with an unflipped one");
    }

    @Test
    public void testPolarityBecomesIndefiniteBelowOtherOperators() {
        final TermTacletAppIndexCacheSet cs = newCacheSet();
        // below an equivalence the polarity is indefinite, whatever the side or history
        assertSame(cs.getAntecCache().descend(eqv, 0), cs.getSuccCache().descend(eqv, 0),
            "indefinite polarity is side-independent");
        assertSame(cs.getAntecCache().descend(not, 0).descend(eqv, 0),
            cs.getSuccCache().descend(eqv, 1),
            "indefinite polarity does not depend on the path that led to it");
        assertNotSame(cs.getAntecCache().descend(eqv, 0), cs.getAntecCache().descend(and, 0),
            "indefinite polarity must not share entries with definite polarity");
    }
}

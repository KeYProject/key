/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.CyclicBarrier;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicReference;

import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.rule.TacletForTests;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.logic.sort.Sort;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * Regression tests for the {@link TermFactory} term interner after it was changed from a
 * single-lock
 * cache to a {@link org.key_project.util.StripedLruCache}. They pin the two behaviours the change
 * must preserve: the cached factory still <em>interns</em> (structurally equal terms created in
 * succession share one instance), and concurrent term creation through the shared per-proof factory
 * stays consistent and exception-free (the whole point of the change is that it does so without the
 * old global lock).
 *
 * @author Claude (KeY multithreading effort)
 */
public class TermFactoryInterningTest {

    private final Sort s1 = new SortImpl(new Name("ITS1"));
    private final Sort s2 = new SortImpl(new Name("ITS2"));
    private final Function p = new JFunction(new Name("p_intern"), JavaDLTheory.FORMULA, s1);
    private final Function r = new JFunction(new Name("r_intern"), JavaDLTheory.FORMULA, s1, s2);
    private final LogicVariable x = new LogicVariable(new Name("x_intern"), s1);
    private final LogicVariable w = new LogicVariable(new Name("w_intern"), s2);

    /** Builds a small fixed set of (cacheable) terms with the given factory. */
    private List<JTerm> buildTerms(TermFactory tf) {
        JTerm tx = tf.createTerm(x);
        JTerm tw = tf.createTerm(w);
        List<JTerm> terms = new ArrayList<>();
        terms.add(tx);
        terms.add(tf.createTerm(p, tx)); // p(x)
        terms.add(tf.createTerm(r, tx, tw)); // r(x, w)
        return terms;
    }

    /** The cached factory must intern: the same term built twice in succession is one instance. */
    @Test
    void cachedFactoryInternsEqualTerms() {
        TermFactory tf = TacletForTests.services().getTermBuilder().tf();
        JTerm a = tf.createTerm(p, tf.createTerm(x));
        JTerm b = tf.createTerm(p, tf.createTerm(x));
        assertEquals(a, b, "structurally equal terms must be equal");
        assertSame(a, b, "the cached factory must return the interned instance");
    }

    /** The uncached factory still produces correct (equal) terms, just not interned. */
    @Test
    void uncachedFactoryStillProducesEqualTerms() {
        TermFactory tf = new TermFactory();
        JTerm a = tf.createTerm(p, tf.createTerm(x));
        JTerm b = tf.createTerm(p, tf.createTerm(x));
        assertEquals(a, b);
    }

    /**
     * Many threads create the same terms through the shared cached factory at once. Every result
     * must equal the single-threaded reference, with no exception or corrupt term -- the striped
     * cache must be as thread-safe as the old globally-synchronized one.
     */
    @Test
    void concurrentTermCreationStaysConsistent() throws Exception {
        TermFactory tf = TacletForTests.services().getTermBuilder().tf();
        List<JTerm> reference = buildTerms(tf);

        final int threads = 16;
        final int rounds = 20_000;
        ExecutorService pool = Executors.newFixedThreadPool(threads);
        AtomicReference<Throwable> failure = new AtomicReference<>();
        CyclicBarrier barrier = new CyclicBarrier(threads);
        List<Future<?>> futures = new ArrayList<>();
        for (int t = 0; t < threads; t++) {
            futures.add(pool.submit(() -> {
                try {
                    barrier.await();
                    for (int i = 0; i < rounds; i++) {
                        List<JTerm> got = buildTerms(tf);
                        for (int k = 0; k < reference.size(); k++) {
                            JTerm g = got.get(k);
                            assertNotNull(g);
                            if (!reference.get(k).equals(g)) {
                                throw new AssertionError(
                                    "term " + k + " differs: " + g + " != " + reference.get(k));
                            }
                        }
                    }
                } catch (Throwable e) {
                    failure.compareAndSet(null, e);
                }
            }));
        }
        for (Future<?> f : futures) {
            f.get(120, TimeUnit.SECONDS);
        }
        pool.shutdownNow();
        if (failure.get() != null) {
            throw new AssertionError("concurrent term creation was inconsistent", failure.get());
        }
    }
}

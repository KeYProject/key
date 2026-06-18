/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.impl;

import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.atomic.AtomicLong;

/**
 * Allocator of fresh symbol names that are globally unique <em>by construction</em> across worker
 * threads, without consulting the shared {@code Namespace} on the hot path.
 *
 * <p>
 * Background (multithreading effort, branch {@code bubel/mt-goals}, Phase 2). When goals are
 * processed concurrently, the classic mint pattern
 * {@code do { name = base + cnt++ } while (namespaces.lookup(name) != null)} races: two workers can
 * both observe {@code base_0} as free and both claim it (a TOCTOU on the shared namespace), so on
 * commit two different symbols end up sharing one name &mdash; unsound. Locking the namespace would
 * fix it but the namespace lookup/add path is performance-critical and must stay lock-free.
 *
 * <p>
 * This allocator removes the race by <strong>partitioning</strong>: each worker draws fresh names
 * from a per-worker, per-base counter and tags names belonging to worker {@code w > 0} with a
 * {@code __t<w>} segment. Thus two workers can never produce the same name even while racing, and
 * no shared namespace read is needed to guarantee that. Worker {@code 0} keeps the legacy
 * (untagged) form so the single-threaded path is unchanged.
 *
 * <p>
 * <b>Contract:</b> names returned by one allocator instance are pairwise distinct. Uniqueness
 * against names that pre-exist in a proof's namespace (e.g. from loading) is <em>not</em> this
 * class's job; the Phase-3 integration composes this allocator with a lock-free lookup in the
 * worker's <em>local</em> namespace for that. The proof fingerprint hashes rule names, not symbol
 * names, so worker-tagged names do not affect the equivalence gate.
 *
 * <p>
 * The current worker is bound per thread via {@link #runAsWorker(int, Runnable)} /
 * {@link #bindWorker(int)}; unbound threads act as worker {@code 0}.
 *
 * @author Claude (KeY multithreading effort)
 */
public final class ParallelNameAllocator {

    /** The worker id bound to the current thread; absent means worker 0 (single-threaded). */
    private static final ThreadLocal<Integer> CURRENT_WORKER = ThreadLocal.withInitial(() -> 0);

    /** Per-{@code (worker,base)} monotonic counters, keyed by {@code worker + "#" + base}. */
    private final ConcurrentMap<String, AtomicLong> counters = new ConcurrentHashMap<>();

    /**
     * Binds the calling thread to a worker id for subsequent {@link #freshName(String)} calls.
     * Prefer {@link #runAsWorker(int, Runnable)} which restores the previous binding.
     *
     * @param workerId a non-negative worker id; {@code 0} is the single-threaded/legacy worker
     */
    public static void bindWorker(int workerId) {
        if (workerId < 0) {
            throw new IllegalArgumentException("worker id must be non-negative: " + workerId);
        }
        CURRENT_WORKER.set(workerId);
    }

    /** Resets the calling thread to the default worker ({@code 0}). */
    public static void unbind() {
        CURRENT_WORKER.remove();
    }

    /** The worker id currently bound to this thread ({@code 0} if none). */
    public static int currentWorker() {
        return CURRENT_WORKER.get();
    }

    /**
     * Runs {@code body} with the calling thread bound to {@code workerId}, restoring the previous
     * binding afterwards.
     *
     * @param workerId the worker id to bind for the duration of {@code body}
     * @param body the work to run
     */
    public static void runAsWorker(int workerId, Runnable body) {
        int previous = CURRENT_WORKER.get();
        bindWorker(workerId);
        try {
            body.run();
        } finally {
            CURRENT_WORKER.set(previous);
        }
    }

    /**
     * Returns a fresh name based on {@code base}, unique among all names produced by this
     * allocator.
     *
     * @param base the base name (e.g. a Skolem symbol stem)
     * @return a unique fresh name, tagged with the current worker unless it is worker 0
     */
    public String freshName(String base) {
        int worker = currentWorker();
        String key = worker + "#" + base;
        long n = counters.computeIfAbsent(key, k -> new AtomicLong()).getAndIncrement();
        // Worker 0 keeps the legacy form (base_n); other workers add a disjoint __t<w> segment so
        // their names can never coincide with another worker's, regardless of n.
        return worker == 0 ? base + "_" + n : base + "_" + n + "__t" + worker;
    }
}

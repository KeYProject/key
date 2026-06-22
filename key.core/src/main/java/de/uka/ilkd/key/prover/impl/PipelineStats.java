/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.impl;

import java.util.concurrent.atomic.AtomicLong;

/**
 * Per-run profiler for the goal-level parallel prover's match-apply-evaluate pipeline (experimental,
 * multithreading effort). It splits every rule step the workers take into four timed phases and a
 * few counts, so a profiling run can attribute wall time to pipeline stages and to lock contention
 * rather than just reporting a total.
 *
 * <p>
 * The four phases (accumulated across all worker threads of one run):
 * <ul>
 * <li><b>select</b> &mdash; matching + strategy cost ({@code getRuleAppManager().next()}): the
 * lock-free "match + evaluate" stage;
 * <li><b>compute</b> &mdash; rule execution / term construction ({@code Goal.computeRuleApp}): the
 * lock-free "apply" stage;
 * <li><b>lockWait</b> &mdash; time a worker is blocked acquiring the commit lock: the contention /
 * serial-fraction proxy (the bigger this is relative to the rest, the worse the proof scales);
 * <li><b>lockHeld</b> &mdash; {@code Goal.commitRuleApp} under the commit lock: the serialized
 * proof-tree mutation (the Amdahl serial section).
 * </ul>
 * Counters: applied steps, aborted applications, stalled goals.
 *
 * <p>
 * <b>Off by default.</b> Only when {@code -Dkey.mt.pipeline=true} does {@link #ENABLED} become true;
 * otherwise {@link ParallelProver} skips the timing entirely (no {@code nanoTime} calls), so there
 * is no overhead on normal/soundness runs. All counters are thread-safe and reset per run.
 *
 * @author Claude (KeY multithreading effort)
 */
public final class PipelineStats {

    /** Whether pipeline profiling is on; set once at class load from {@code -Dkey.mt.pipeline}. */
    public static final boolean ENABLED = Boolean.getBoolean("key.mt.pipeline");

    /** The process-wide profiler (one parallel run is active at a time; workers update atomically). */
    public static final PipelineStats GLOBAL = new PipelineStats();

    /** CSV header fragment (the columns {@link #csvRow()} emits), without surrounding commas. */
    public static final String CSV_HEADER =
        "selectMs,computeMs,lockWaitMs,lockHeldMs,appliedSteps,aborts,stalls";
    /** A zero row matching {@link #CSV_HEADER}, for runs where profiling was off. */
    public static final String ZERO_ROW = "0,0,0,0,0,0,0";

    private final AtomicLong selectNanos = new AtomicLong();
    private final AtomicLong computeNanos = new AtomicLong();
    private final AtomicLong lockWaitNanos = new AtomicLong();
    private final AtomicLong lockHeldNanos = new AtomicLong();
    private final AtomicLong applied = new AtomicLong();
    private final AtomicLong aborts = new AtomicLong();
    private final AtomicLong stalls = new AtomicLong();

    /** Clears all phase timers and counters for the next run. */
    public void reset() {
        selectNanos.set(0);
        computeNanos.set(0);
        lockWaitNanos.set(0);
        lockHeldNanos.set(0);
        applied.set(0);
        aborts.set(0);
        stalls.set(0);
    }

    public void addSelect(long nanos) {
        selectNanos.addAndGet(nanos);
    }

    public void addCompute(long nanos) {
        computeNanos.addAndGet(nanos);
    }

    public void addLockWait(long nanos) {
        lockWaitNanos.addAndGet(nanos);
    }

    public void addLockHeld(long nanos) {
        lockHeldNanos.addAndGet(nanos);
    }

    public void incApplied() {
        applied.incrementAndGet();
    }

    public void incAborts() {
        aborts.incrementAndGet();
    }

    public void incStalls() {
        stalls.incrementAndGet();
    }

    public long selectMs() {
        return selectNanos.get() / 1_000_000L;
    }

    public long computeMs() {
        return computeNanos.get() / 1_000_000L;
    }

    public long lockWaitMs() {
        return lockWaitNanos.get() / 1_000_000L;
    }

    public long lockHeldMs() {
        return lockHeldNanos.get() / 1_000_000L;
    }

    public long appliedSteps() {
        return applied.get();
    }

    public long aborts() {
        return aborts.get();
    }

    public long stalls() {
        return stalls.get();
    }

    /** Sum of the four phase times, in ms (the profiled work; aggregated over all workers). */
    public long totalMs() {
        return selectMs() + computeMs() + lockWaitMs() + lockHeldMs();
    }

    /** CSV row matching {@link #CSV_HEADER}. */
    public String csvRow() {
        return selectMs() + "," + computeMs() + "," + lockWaitMs() + "," + lockHeldMs() + ","
            + applied.get() + "," + aborts.get() + "," + stalls.get();
    }
}

/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.mt;

import java.io.BufferedWriter;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadInfo;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.impl.ParallelProver;
import de.uka.ilkd.key.prover.impl.PipelineStats;
import de.uka.ilkd.key.util.ProofStarter;

import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIfSystemProperty;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * One-shot, high-core stress battery for the goal-level parallel prover. Built for a single run on
 * a
 * many-core machine (e.g. 128 cores): it cannot easily be repeated, so it errs on the side of
 * collecting as much diagnostic information as possible whenever something goes wrong, so a race or
 * hang can be traced down afterwards.
 *
 * <p>
 * For every proof in a (diverse, optionally saturating) corpus it first proves the obligation
 * <em>single-threaded</em> to obtain a reference outcome (closed/open + a structural fingerprint),
 * then proves it on the multi-core prover across a range of worker counts (including counts that
 * over-subscribe the machine, which maximises interleaving) and many repetitions. Each multi-core
 * run is compared to the reference and classified:
 * <ul>
 * <li><b>OK</b> — same closed/open outcome, no error.
 * <li><b>NONCLOSURE</b> — the reference closed but this run left goals open (the classic lost-goal
 * race). The open goals are dumped with, for each, whether it still has an applicable rule — a goal
 * that is open <em>and</em> has an applicable rule was wrongly abandoned.
 * <li><b>UNSOUND_CLOSE</b> — this run closed but the single-threaded reference did not (must never
 * happen for a sound prover).
 * <li><b>EXCEPTION</b> — the run threw, or the prover reported an error (e.g. a concurrent-state
 * {@code IndexOutOfBoundsException} in matching). The full stack is captured.
 * <li><b>HANG</b> — the run exceeded the per-run timeout (deadlock / lost wake-up). A full thread
 * dump of every JVM thread is captured <em>while the threads are still stuck</em>, then the current
 * proof is abandoned (its child JVM is likely wedged) and the orchestrator moves on to the next.
 * <li><b>DIVERGE</b> — both closed but with a different (sibling-order-insensitive) structure.
 * Sound
 * but non-deterministic; recorded for information, not counted as a failure.
 * </ul>
 *
 * <p>
 * <b>Each proof runs in its own forked JVM.</b> The {@link #stress()} test is only an orchestrator:
 * for every corpus entry it launches a fresh child JVM (re-entering this class via {@link #main})
 * that proves <em>that one</em> obligation across all worker counts, then it aggregates the
 * children's output. This gives two properties the one-shot 128-core run lacked: (1) <b>memory
 * isolation</b> — a growing live set / static-cache accumulation in one proof cannot leak into the
 * next (the first run was GC-bound, spending most of its wall time in full GCs with a steadily
 * growing heap); and (2) <b>hang survival</b> — a child that wedges (e.g. a GC death-spiral the
 * in-JVM watchdog cannot escape) is killed after a per-proof process timeout and the battery
 * continues with the next proof, instead of aborting the whole matrix. Set
 * {@code -Dkey.mt.stresstest.fork=false} to run everything in-process (the old single-JVM
 * behaviour,
 * handy for quick local checks).
 *
 * <p>
 * Output goes to {@code build/mt-stress/} (override with {@code -Dkey.mt.stresstest.out}): a
 * {@code runs.csv} with one row per run, one {@code fail_*.txt} per anomaly with the full
 * diagnostics, and a {@code summary.txt}. Each child first writes its own {@code runs-<tag>.csv}
 * and
 * {@code summary-<tag>.txt}; the orchestrator concatenates these into the top-level files. The
 * battery runs to completion (it does not stop at the first failure, except for a hang within a
 * proof) and only then fails the test if any anomaly was seen, so all data is on disk regardless.
 *
 * <p>
 * Enable with {@code -Dkey.mt.stresstest=true}. Knobs (all optional):
 * <ul>
 * <li>{@code -Dkey.mt.stresstest.proofs} — comma-separated corpus. An entry is either an
 * example-relative {@code .key} path, or a generated problem {@code synthetic:split_ifs:<n>} /
 * {@code synthetic:split_work:<n>:<work>} (wide fan-out, good for saturating many workers).
 * <li>{@code -Dkey.mt.stresstest.workers} — comma-separated worker counts (default
 * {@code 1,2,4,8,16,32,64,128,192,256}); not clamped to the core count, deliberately.
 * <li>{@code -Dkey.mt.stresstest.reps} — repetitions per (proof, workers) cell (default 20).
 * <li>{@code -Dkey.mt.stresstest.timeout} — per-run hang timeout in seconds (default 600).
 * <li>{@code -Dkey.mt.stresstest.proctimeout} — per-proof <em>process</em> timeout in seconds
 * (default 7200); a child exceeding it is force-killed and recorded as a {@code PROCESS-HANG}.
 * <li>{@code -Dkey.mt.stresstest.childheap} — {@code -Xmx} for each child JVM (e.g. {@code 32g});
 * if
 * unset the child inherits the default heap.
 * <li>{@code -Dkey.mt.stresstest.jfrdir} — if set, every child records its own
 * {@code <tag>.jfr} Flight Recording there (per-proof recordings, instead of one rolling file).
 * <li>{@code -Dkey.mt.stresstest.fork} — {@code false} to run in-process in a single JVM.
 * <li>{@code -Dkey.mt.stresstest.forkpercell} — {@code true} to fork a fresh JVM per
 * <em>(proof, worker-count)</em> cell instead of per proof. Each child then does only a reference
 * run plus {@code reps} runs, which bounds the cross-run memory growth (a pre-existing KeY
 * proof-retention leak) that otherwise accumulates over a proof's hundreds of runs and tips a heavy
 * proof's child into a GC death-spiral at high worker counts. Costs extra JVM starts and one
 * reference run per cell; recommended for long, high-rep or high-worker runs.
 * </ul>
 * Run under {@code -ea} (assertions on). To force the legacy cursor-based find-matcher (instead of
 * the default compiled one), pass {@code -Dkey.matcher.interpreter=true} (forwarded to the
 * children).
 *
 * @author Claude (KeY multithreading effort)
 */
@EnabledIfSystemProperty(named = "key.mt.stresstest", matches = "true")
public class MtStressMatrix {

    private static final String DEFAULT_CORPUS = String.join(",",
        "synthetic:split_ifs:13", // ~8192 cheap independent leaves -- saturates many workers
        "synthetic:split_work:8:150", // 256 leaves each with real work -- concurrent
                                      // matching+commit
        "standard_key/java_dl/symmArray.key",
        "heap/list/ArrayList_concatenate.key",
        "heap/list_seq/SimplifiedLinkedList.remove.key",
        "heap/saddleback_search/Saddleback_search.key",
        "heap/observer/ExampleSubject_addObserver.key",
        "standard_key/arith/median.key",
        "heap/coincidence_count/project.key");

    private static final String DEFAULT_WORKERS = "1,2,4,8,16,32,64,128,192,256";

    private static final String CSV_HEADER =
        "proof,workers,rep,status,closed,refClosed,nodes,branches,openGoals,timeMs,"
            + "reason,canonicalDigest,refCanonicalDigest," + PipelineStats.CSV_HEADER + "\n";

    /** Outcome classification of one run. */
    private enum Status {
        OK, DIVERGE, NONCLOSURE, UNSOUND_CLOSE, EXCEPTION, HANG, REF_FAILED
    }

    /** Everything recorded for a single run. */
    private static final class Run {
        Status status = Status.OK;
        boolean closed;
        int nodes;
        int branches;
        int openGoals;
        long timeMs;
        String reason = "";
        String orderedDigest = "";
        String canonicalDigest = "";
        String openGoalDetails = ""; // serialNr : hasApplicableRule per open goal
        Throwable exception;
        String threadDump = "";
        // Pipeline profiler totals for this run (0 unless -Dkey.mt.pipeline=true). See PipelineStats.
        long selectMs;
        long computeMs;
        long lockWaitMs;
        long lockHeldMs;
        String pipelineCsv = PipelineStats.ZERO_ROW;
    }

    /**
     * Orchestrator: forks one child JVM per corpus entry (each child re-enters via {@link #main}
     * and
     * proves a single obligation across all worker counts), then aggregates. With
     * {@code -Dkey.mt.stresstest.fork=false} it instead runs every proof in-process.
     */
    @Test
    void stress() throws Exception {
        String[] corpus = System.getProperty("key.mt.stresstest.proofs", DEFAULT_CORPUS).split(",");
        boolean fork = Boolean.parseBoolean(System.getProperty("key.mt.stresstest.fork", "true"));
        // Per-cell mode forks a fresh JVM per (proof, worker-count) instead of per proof, so each
        // child only does REF + reps runs. This bounds the cross-run memory accumulation (a
        // pre-existing KeY proof-retention leak) that otherwise builds up over a proof's hundreds
        // of
        // runs and tips a heavy proof's child into a GC death-spiral at high worker counts. Costs
        // extra JVM starts and one reference run per cell.
        boolean forkPerCell =
            Boolean.parseBoolean(System.getProperty("key.mt.stresstest.forkpercell", "false"));
        long procTimeoutMs = Long.getLong("key.mt.stresstest.proctimeout", 7200L) * 1000L;
        Path outDir = Path.of(System.getProperty("key.mt.stresstest.out", "build/mt-stress"));
        Files.createDirectories(outDir);

        int cores = Runtime.getRuntime().availableProcessors();
        log("[mt-stress] orchestrator: cores=%d proofs=%d fork=%s perCell=%s procTimeout=%ds out=%s",
            cores, corpus.length, fork, forkPerCell, procTimeoutMs / 1000, outDir.toAbsolutePath());
        log("[mt-stress] corpus: %s", String.join(" | ", corpus));

        List<String> anomalies = new ArrayList<>();
        long wall0 = System.currentTimeMillis();

        for (String spec : corpus) {
            spec = spec.trim();
            if (fork && forkPerCell) {
                int[] workers =
                    parseInts(System.getProperty("key.mt.stresstest.workers", DEFAULT_WORKERS));
                for (int w : workers) {
                    log("[mt-stress] === %s @ %d workers : forking child JVM ===", shortName(spec),
                        w);
                    ForkOutcome o = forkChild(spec, outDir, procTimeoutMs, w);
                    String cell = shortName(spec) + "@" + w;
                    if (o.timedOut) {
                        anomalies.add("PROCESS-HANG " + cell + " (killed after " + procTimeoutMs
                                / 1000
                            + "s; child JVM wedged)");
                    } else if (o.exit != 0) {
                        anomalies.add("CHILD-ANOMALY " + cell + " (child exit=" + o.exit + ")");
                    }
                }
            } else if (fork) {
                log("[mt-stress] === %s : forking child JVM ===", shortName(spec));
                ForkOutcome o = forkChild(spec, outDir, procTimeoutMs, -1);
                if (o.timedOut) {
                    anomalies.add("PROCESS-HANG " + shortName(spec) + " (killed after "
                        + procTimeoutMs / 1000 + "s; child JVM wedged)");
                } else if (o.exit != 0) {
                    anomalies.add("CHILD-ANOMALY " + shortName(spec) + " (child exit=" + o.exit
                        + "; see fail_*.txt / summary-" + tagOf(spec) + ".txt)");
                }
            } else {
                int rc = runOneProof(spec, FindResources.getExampleDirectory(),
                    parseInts(System.getProperty("key.mt.stresstest.workers", DEFAULT_WORKERS)),
                    Integer.getInteger("key.mt.stresstest.reps", 20),
                    Long.getLong("key.mt.stresstest.timeout", 600L) * 1000L, outDir, tagOf(spec));
                if (rc != 0) {
                    anomalies.add("ANOMALY " + shortName(spec) + " (see summary-" + tagOf(spec)
                        + ".txt)");
                }
            }
        }

        long wallSecs = (System.currentTimeMillis() - wall0) / 1000;
        aggregate(outDir, anomalies, wallSecs);

        assertTrue(anomalies.isEmpty(),
            () -> "multi-core stress found " + anomalies.size() + " proof(s) with anomalies; see "
                + outDir.toAbsolutePath());
    }

    /** Child entry point: prove the single obligation named by {@code args[0]} and exit. */
    public static void main(String[] args) throws Exception {
        String spec = args.length > 0 ? args[0].trim()
                : System.getProperty("key.mt.stresstest.proofs", "").trim();
        int[] workers = parseInts(System.getProperty("key.mt.stresstest.workers", DEFAULT_WORKERS));
        int reps = Integer.getInteger("key.mt.stresstest.reps", 20);
        long timeoutMs = Long.getLong("key.mt.stresstest.timeout", 600L) * 1000L;
        Path outDir = Path.of(System.getProperty("key.mt.stresstest.out", "build/mt-stress"));
        Files.createDirectories(outDir);
        // In per-cell mode the orchestrator gives each child a distinct output tag so the
        // runs-<tag>.csv / summary-<tag>.txt of different worker counts of the same proof do not
        // clobber each other; otherwise it is just the proof tag.
        String outTag = System.getProperty("key.mt.stresstest.outtag", tagOf(spec));
        int rc =
            new MtStressMatrix().runOneProof(spec, FindResources.getExampleDirectory(), workers,
                reps, timeoutMs, outDir, outTag);
        System.out.flush();
        System.exit(rc);
    }

    /** Result of waiting on a forked child. */
    private record ForkOutcome(int exit, boolean timedOut) {
    }

    /**
     * Launches a child JVM and waits for it (force-killing it past the timeout). When
     * {@code singleWorker > 0} the child runs only that one worker count (per-cell mode) and writes
     * to a worker-count-tagged output file; otherwise it runs the whole worker-count list.
     */
    private ForkOutcome forkChild(String spec, Path outDir, long procTimeoutMs, int singleWorker)
            throws Exception {
        boolean perCell = singleWorker > 0;
        String cellTag = perCell ? tagOf(spec) + "_w" + singleWorker : tagOf(spec);
        String label = perCell ? shortName(spec) + "@" + singleWorker : shortName(spec);

        List<String> cmd = new ArrayList<>();
        cmd.add(Path.of(System.getProperty("java.home"), "bin", "java").toString());
        cmd.add("-cp");
        cmd.add(System.getProperty("java.class.path"));
        cmd.add("-ea");
        String heap = System.getProperty("key.mt.stresstest.childheap", "");
        if (!heap.isBlank()) {
            cmd.add("-Xmx" + heap);
        }
        String jfrDir = System.getProperty("key.mt.stresstest.jfrdir");
        if (jfrDir != null) {
            Files.createDirectories(Path.of(jfrDir));
            Path jf = Path.of(jfrDir, cellTag + ".jfr");
            cmd.add("-XX:StartFlightRecording=filename=" + jf
                + ",settings=profile,dumponexit=true,disk=true");
            cmd.add("-XX:FlightRecorderOptions=stackdepth=128");
        }
        // Resource-locating and matcher properties the child needs (Gradle sets these on us, but a
        // forked JVM does not inherit -D from its parent, so pass them explicitly).
        for (String p : new String[] { "EXAMPLES_DIR", "test-resources", "testcases",
            "TACLET_PROOFS", "key.disregardSettings", "key.matcher.interpreter" }) {
            String v = System.getProperty(p);
            if (v != null) {
                cmd.add("-D" + p + "=" + v);
            }
        }
        cmd.add("-Dkey.mt.stresstest=true");
        cmd.add("-Dkey.mt.stresstest.out=" + outDir);
        for (String p : new String[] { "key.mt.stresstest.workers", "key.mt.stresstest.reps",
            "key.mt.stresstest.timeout", "key.mt.stresstest.maxsteps", "key.mt.pipeline" }) {
            String v = System.getProperty(p);
            if (v != null) {
                cmd.add("-D" + p + "=" + v);
            }
        }
        if (perCell) {
            // Override the worker list with the single cell and give the child a distinct output
            // tag.
            cmd.add("-Dkey.mt.stresstest.workers=" + singleWorker);
            cmd.add("-Dkey.mt.stresstest.outtag=" + cellTag);
        }
        cmd.add(MtStressMatrix.class.getName());
        cmd.add(spec);

        ProcessBuilder pb = new ProcessBuilder(cmd)
                .redirectOutput(ProcessBuilder.Redirect.INHERIT)
                .redirectError(ProcessBuilder.Redirect.INHERIT);
        long t0 = System.currentTimeMillis();
        Process p = pb.start();
        if (!p.waitFor(procTimeoutMs, TimeUnit.MILLISECONDS)) {
            p.descendants().forEach(ProcessHandle::destroyForcibly);
            p.destroyForcibly();
            p.waitFor(60, TimeUnit.SECONDS);
            log("[mt-stress]   !! %s exceeded the %ds process timeout -> killed", label,
                procTimeoutMs / 1000);
            return new ForkOutcome(-1, true);
        }
        int exit = p.exitValue();
        log("[mt-stress]   %s child exit=%d (%ds)", label, exit,
            (System.currentTimeMillis() - t0) / 1000);
        return new ForkOutcome(exit, false);
    }

    /**
     * Proves one obligation across all worker counts, writing this proof's {@code runs-<tag>.csv}
     * and {@code summary-<tag>.txt}. Returns 0 if clean, non-zero if any anomaly (or a hang) was
     * seen.
     */
    private int runOneProof(String spec, Path examples, int[] workers, int reps, long timeoutMs,
            Path outDir, String outTag) throws Exception {
        String tag = outTag;
        int cores = Runtime.getRuntime().availableProcessors();
        long maxHeap = Runtime.getRuntime().maxMemory() / (1024 * 1024);
        log("[mt-stress:%s] cores=%d maxHeap=%dMB workers=%s reps=%d timeout=%ds", tag, cores,
            maxHeap, Arrays.toString(workers), reps, timeoutMs / 1000);

        List<String> anomalies = new ArrayList<>();
        Map<String, int[]> tally = new LinkedHashMap<>(); // "proof@workers" -> per-status counts
        int totalRuns = 0;
        boolean hangAbort = false;
        long wall0 = System.currentTimeMillis();

        try (BufferedWriter csv = Files.newBufferedWriter(outDir.resolve("runs-" + tag + ".csv"))) {
            csv.write(CSV_HEADER);

            // Single-threaded reference.
            Run ref = runWithWatchdog(spec, examples, 0, timeoutMs);
            boolean refUsable = ref.status != Status.HANG && ref.status != Status.EXCEPTION;
            log("[mt-stress:%s] REF closed=%s nodes=%d openGoals=%d reason=%s", tag,
                refUsable ? ref.closed : "??", ref.nodes, ref.openGoals,
                refUsable ? ref.reason : ref.status);
            if (!refUsable) {
                String f = writeDiagnostics(outDir, spec, 0, -1, ref, ref);
                anomalies.add("REF " + spec + " -> " + f);
            } else {
                runs: for (int w : workers) {
                    int[] counts = new int[Status.values().length];
                    long pSel = 0;
                    long pComp = 0;
                    long pWait = 0;
                    long pHeld = 0;
                    int pRuns = 0;
                    for (int rep = 0; rep < reps; rep++) {
                        Run r = runWithWatchdog(spec, examples, w, timeoutMs);
                        r.status = classify(r, ref);
                        counts[r.status.ordinal()]++;
                        totalRuns++;
                        csv.write(String.format("%s,%d,%d,%s,%s,%s,%d,%d,%d,%d,%s,%s,%s,%s%n",
                            shortName(spec), w, rep, r.status, r.closed, ref.closed, r.nodes,
                            r.branches, r.openGoals, r.timeMs, csvSafe(r.reason), r.canonicalDigest,
                            ref.canonicalDigest, r.pipelineCsv));
                        csv.flush();
                        pSel += r.selectMs;
                        pComp += r.computeMs;
                        pWait += r.lockWaitMs;
                        pHeld += r.lockHeldMs;
                        pRuns++;
                        if (isAnomaly(r.status)) {
                            String f = writeDiagnostics(outDir, spec, w, rep, r, ref);
                            anomalies.add(r.status + " " + shortName(spec) + " w=" + w + " rep="
                                + rep + " -> " + f);
                            log("[mt-stress:%s]   !! %s w=%d rep=%d -> %s", tag, r.status, w, rep,
                                f);
                        }
                        if (r.status == Status.HANG) {
                            // A hang only aborts THIS proof; the orchestrator moves on to the next
                            // (in its own fresh JVM).
                            hangAbort = true;
                            break runs;
                        }
                    }
                    tally.put(shortName(spec) + "@" + w, counts);
                    log("[mt-stress:%s] w=%-4d ok=%d diverge=%d nonclosure=%d exception=%d", tag, w,
                        counts[Status.OK.ordinal()], counts[Status.DIVERGE.ordinal()],
                        counts[Status.NONCLOSURE.ordinal()], counts[Status.EXCEPTION.ordinal()]);
                    if (PipelineStats.ENABLED && pRuns > 0) {
                        long tot = pSel + pComp + pWait + pHeld;
                        log("[mt-stress:%s] w=%-4d pipeline(mean ms): select=%d compute=%d "
                            + "lockWait=%d lockHeld=%d | serial=%.0f%% contention=%.0f%%", tag, w,
                            pSel / pRuns, pComp / pRuns, pWait / pRuns, pHeld / pRuns,
                            tot == 0 ? 0.0 : 100.0 * pHeld / tot,
                            tot == 0 ? 0.0 : 100.0 * pWait / tot);
                    }
                }
            }
        }

        StringBuilder sum = new StringBuilder();
        sum.append(String.format("[%s] runs=%d anomalies=%d wall=%ds%s%n", tag, totalRuns,
            anomalies.size(), (System.currentTimeMillis() - wall0) / 1000,
            hangAbort ? "  (proof aborted on a hang)" : ""));
        for (var e : tally.entrySet()) {
            int[] c = e.getValue();
            sum.append(
                String.format("  %-52s ok=%d diverge=%d nonclosure=%d unsound=%d exception=%d%n",
                    e.getKey(), c[Status.OK.ordinal()], c[Status.DIVERGE.ordinal()],
                    c[Status.NONCLOSURE.ordinal()], c[Status.UNSOUND_CLOSE.ordinal()],
                    c[Status.EXCEPTION.ordinal()]));
        }
        if (!anomalies.isEmpty()) {
            sum.append("  ANOMALIES:\n");
            for (String a : anomalies) {
                sum.append("    ").append(a).append('\n');
            }
        }
        Files.writeString(outDir.resolve("summary-" + tag + ".txt"), sum);
        System.out.println(sum);
        return (anomalies.isEmpty() && !hangAbort) ? 0 : 1;
    }

    /**
     * Concatenates every per-proof / per-cell {@code runs-*.csv} and {@code summary-*.txt} the
     * children wrote into the top-level {@code runs.csv} / {@code summary.txt}. Globbing (rather
     * than
     * walking the corpus) makes it agnostic to per-proof vs per-cell forking.
     */
    private void aggregate(Path outDir, List<String> parentAnomalies, long wallSecs)
            throws Exception {
        List<Path> runFiles = sortedMatches(outDir, "runs-", ".csv");
        try (BufferedWriter csv = Files.newBufferedWriter(outDir.resolve("runs.csv"))) {
            csv.write(CSV_HEADER);
            for (Path pf : runFiles) {
                List<String> lines = Files.readAllLines(pf);
                for (int i = 1; i < lines.size(); i++) { // skip the per-file header
                    csv.write(lines.get(i));
                    csv.write("\n");
                }
            }
        }

        StringBuilder sum = new StringBuilder();
        sum.append("[mt-stress] SUMMARY (forked JVMs)\n");
        sum.append(String.format("cells=%d  cellsWithAnomaly=%d  wall=%ds%n", runFiles.size(),
            parentAnomalies.size(), wallSecs));
        for (Path sf : sortedMatches(outDir, "summary-", ".txt")) {
            sum.append(Files.readString(sf));
        }
        if (!parentAnomalies.isEmpty()) {
            sum.append("ANOMALIES:\n");
            for (String a : parentAnomalies) {
                sum.append("  ").append(a).append('\n');
            }
        }
        Files.writeString(outDir.resolve("summary.txt"), sum);
        System.out.println(sum);
    }

    /**
     * Sorted list of files in {@code dir} whose name starts with {@code prefix} and ends suffix.
     */
    private static List<Path> sortedMatches(Path dir, String prefix, String suffix)
            throws Exception {
        try (var s = Files.list(dir)) {
            return s.filter(p -> {
                String n = p.getFileName().toString();
                return n.startsWith(prefix) && n.endsWith(suffix);
            }).sorted().collect(java.util.stream.Collectors.toList());
        }
    }

    /** Runs one configuration on its own thread, guarded by a hang timeout. */
    private Run runWithWatchdog(String spec, Path examples, int workers, long timeoutMs) {
        ExecutorService ex = Executors.newSingleThreadExecutor(r -> {
            Thread t = new Thread(r, "mt-stress-run");
            t.setDaemon(true);
            return t;
        });
        Future<Run> f = ex.submit(() -> runOnce(spec, examples, workers));
        try {
            return f.get(timeoutMs, TimeUnit.MILLISECONDS);
        } catch (TimeoutException te) {
            // Capture every thread's stack NOW, while the workers are still stuck.
            Run r = new Run();
            r.status = Status.HANG;
            r.threadDump = allThreadsDump();
            f.cancel(true);
            return r;
        } catch (ExecutionException ee) {
            Run r = new Run();
            r.status = Status.EXCEPTION;
            r.exception = ee.getCause() != null ? ee.getCause() : ee;
            return r;
        } catch (InterruptedException ie) {
            Thread.currentThread().interrupt();
            Run r = new Run();
            r.status = Status.EXCEPTION;
            r.exception = ie;
            return r;
        } finally {
            ex.shutdownNow();
        }
    }

    /** Loads and proves once; {@code workers == 0} is the single-threaded reference. */
    private Run runOnce(String spec, Path examples, int workers) throws Exception {
        Run r = new Run();
        Path keyFile = resolve(spec, examples);
        String prevEnabled = System.getProperty(ParallelProver.PARALLEL_PROPERTY);
        String prevThreads = System.getProperty(ParallelProver.THREADS_PROPERTY);
        if (workers > 0) {
            System.setProperty(ParallelProver.PARALLEL_PROPERTY, "true");
            System.setProperty(ParallelProver.THREADS_PROPERTY, Integer.toString(workers));
        } else {
            System.clearProperty(ParallelProver.PARALLEL_PROPERTY);
        }
        KeYEnvironment<?> env = KeYEnvironment.load(keyFile);
        try {
            Proof proof = env.getLoadedProof();
            ProofStarter starter = new ProofStarter(false);
            starter.init(proof);
            int maxSteps = Integer.getInteger("key.mt.stresstest.maxsteps", 0);
            if (maxSteps > 0) {
                starter.setMaxRuleApplications(maxSteps);
            }
            PipelineStats.GLOBAL.reset();
            long t0 = System.nanoTime();
            var info = starter.start();
            r.timeMs = (System.nanoTime() - t0) / 1_000_000L;
            r.selectMs = PipelineStats.GLOBAL.selectMs();
            r.computeMs = PipelineStats.GLOBAL.computeMs();
            r.lockWaitMs = PipelineStats.GLOBAL.lockWaitMs();
            r.lockHeldMs = PipelineStats.GLOBAL.lockHeldMs();
            r.pipelineCsv = PipelineStats.GLOBAL.csvRow();
            ProofFingerprint fp = ProofFingerprint.of(proof);
            r.closed = fp.closed;
            r.nodes = fp.nodeCount;
            r.branches = fp.branchCount;
            r.openGoals = fp.openGoals;
            r.orderedDigest = fp.orderedDigest;
            r.canonicalDigest = fp.canonicalDigest;
            r.reason = String.valueOf(info.reason());
            if (info.isError()) {
                r.exception = info.getException();
            }
            r.openGoalDetails = openGoalDetails(proof);
            return r;
        } finally {
            restore(ParallelProver.PARALLEL_PROPERTY, prevEnabled);
            restore(ParallelProver.THREADS_PROPERTY, prevThreads);
            env.dispose();
        }
    }

    private static Status classify(Run r, Run ref) {
        if (r.status == Status.HANG) {
            return Status.HANG;
        }
        if (r.exception != null) {
            return Status.EXCEPTION;
        }
        if (r.closed && !ref.closed) {
            return Status.UNSOUND_CLOSE;
        }
        if (!r.closed && ref.closed) {
            return Status.NONCLOSURE;
        }
        if (r.closed && ref.closed && !r.canonicalDigest.equals(ref.canonicalDigest)) {
            return Status.DIVERGE; // sound but a structurally different proof (non-determinism)
        }
        return Status.OK;
    }

    private static boolean isAnomaly(Status s) {
        return s == Status.NONCLOSURE || s == Status.UNSOUND_CLOSE || s == Status.EXCEPTION
                || s == Status.HANG;
    }

    /** Per-anomaly diagnostics file; returns its name. */
    private String writeDiagnostics(Path outDir, String spec, int workers, int rep, Run r, Run ref)
            throws Exception {
        String name =
            String.format("fail_%s_w%d_rep%d_%s.txt", shortName(spec).replaceAll("\\W+", "_"),
                workers, rep, r.status);
        StringBuilder b = new StringBuilder();
        b.append("=== MULTI-CORE STRESS ANOMALY ===\n");
        b.append("proof=").append(spec).append("  workers=").append(workers).append("  rep=")
                .append(rep).append("  status=").append(r.status).append('\n');
        b.append(
            String.format("closed=%s refClosed=%s nodes=%d branches=%d openGoals=%d time=%dms%n",
                r.closed, ref.closed, r.nodes, r.branches, r.openGoals, r.timeMs));
        b.append("reason=").append(r.reason).append('\n');
        b.append("fingerprint   ordered=").append(r.orderedDigest).append(" canonical=")
                .append(r.canonicalDigest).append('\n');
        b.append("ref fingerprint ordered=").append(ref.orderedDigest).append(" canonical=")
                .append(ref.canonicalDigest).append('\n');
        if (!r.openGoalDetails.isBlank()) {
            b.append("--- open goals (serialNr : hasApplicableRule) ---\n");
            b.append(r.openGoalDetails).append('\n');
            b.append("(an open goal that still HAS an applicable rule was wrongly abandoned)\n");
        }
        if (r.exception != null) {
            b.append("--- exception ---\n").append(stackTrace(r.exception)).append('\n');
        }
        if (!r.threadDump.isBlank()) {
            b.append("--- thread dump (all JVM threads, captured during the hang) ---\n");
            b.append(r.threadDump).append('\n');
        }
        Path file = outDir.resolve(name);
        Files.writeString(file, b);
        return name;
    }

    private static String openGoalDetails(Proof proof) {
        StringBuilder b = new StringBuilder();
        int i = 0;
        for (Goal g : proof.openGoals()) {
            if (i++ >= 200) {
                b.append("... (truncated)\n");
                break;
            }
            b.append("  goal node ").append(g.node().serialNr()).append(" : hasApplicableRule=")
                    .append(Goal.hasApplicableRules(g)).append('\n');
        }
        return b.toString();
    }

    private static String allThreadsDump() {
        StringBuilder b = new StringBuilder();
        ThreadInfo[] infos =
            ManagementFactory.getThreadMXBean().dumpAllThreads(true, true);
        b.append(infos.length).append(" threads\n");
        for (ThreadInfo ti : infos) {
            b.append(ti.toString()); // includes name, state, lock info and the stack
        }
        return b.toString();
    }

    private static String stackTrace(Throwable t) {
        StringWriter sw = new StringWriter();
        t.printStackTrace(new PrintWriter(sw));
        return sw.toString();
    }

    /** Resolves an example-relative path, or generates a synthetic problem into a temp file. */
    private Path resolve(String spec, Path examples) throws Exception {
        spec = spec.trim();
        if (spec.startsWith("synthetic:")) {
            String[] p = spec.split(":");
            String content;
            String tag;
            if (p[1].equals("split_ifs")) {
                content = MtSyntheticBenchmark.splitIfs(Integer.parseInt(p[2]));
                tag = "split_ifs_" + p[2];
            } else if (p[1].equals("split_work")) {
                content =
                    MtSyntheticBenchmark.splitWork(Integer.parseInt(p[2]), Integer.parseInt(p[3]));
                tag = "split_work_" + p[2] + "_" + p[3];
            } else {
                throw new IllegalArgumentException("unknown synthetic problem: " + spec);
            }
            Path tmp = Files.createTempFile("mt-stress-" + tag, ".key");
            tmp.toFile().deleteOnExit();
            Files.writeString(tmp, content);
            return tmp;
        }
        return examples.resolve(spec);
    }

    private static String shortName(String spec) {
        if (spec.startsWith("synthetic:")) {
            return spec.substring("synthetic:".length());
        }
        int slash = spec.lastIndexOf('/');
        return slash < 0 ? spec : spec.substring(slash + 1);
    }

    /** Filesystem-safe per-proof tag used for {@code runs-<tag>.csv}, {@code <tag>.jfr}, etc. */
    private static String tagOf(String spec) {
        return shortName(spec).replaceAll("\\W+", "_");
    }

    private static String csvSafe(String s) {
        return s == null ? "" : s.replace(',', ';').replace('\n', ' ').trim();
    }

    private static int[] parseInts(String csv) {
        String[] parts = csv.split("\\s*,\\s*");
        int[] r = new int[parts.length];
        for (int i = 0; i < parts.length; i++) {
            r[i] = Integer.parseInt(parts[i].trim());
        }
        return r;
    }

    private static void restore(String key, String previous) {
        if (previous == null) {
            System.clearProperty(key);
        } else {
            System.setProperty(key, previous);
        }
    }

    private static void log(String fmt, Object... args) {
        System.out.printf(fmt + "%n", args);
    }
}

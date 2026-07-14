/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.mt;

import java.lang.management.ManagementFactory;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Comparator;
import java.util.Map;
import java.util.TreeMap;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.ProofStarter;

import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIfSystemProperty;

/**
 * Measures whether memory accumulates <em>across</em> repeated load/prove/dispose cycles of the
 * same obligation in one JVM. The 128-core stress run #1 was GC-bound with a steadily growing ~17
 * GB
 * live set, which suggested per-proof state was retained after {@link KeYEnvironment#dispose()}
 * rather
 * than something intrinsic to the parallel prover; this probe isolates that on a single thread.
 *
 * <p>
 * It proves the obligation {@code reps} times, and after each cycle forces a full GC and records
 * the
 * live heap. A flat trend means {@code dispose()} releases everything; a rising trend quantifies
 * the
 * leak (MB per proof). With {@code -Dkey.mt.retention.histo=true} it additionally prints, at the
 * end,
 * the classes whose live-instance count grew the most between an early and the final cycle (a cheap
 * "what is being retained" histogram via the diagnostic command on this JVM).
 *
 * <p>
 * Enable with {@code -Dkey.mt.retention=true}. Knobs: {@code -Dkey.mt.retention.proof} (example
 * relative, default symmArray), {@code -Dkey.mt.retention.reps} (default 12),
 * {@code -Dkey.mt.retention.histo} (default false). Run with a fixed, modest {@code -Xmx} so growth
 * is visible (e.g. {@code -PstressHeap} on the dedicated task), single-threaded by default.
 *
 */
@EnabledIfSystemProperty(named = "key.mt.retention", matches = "true")
public class MtRetentionProbe {

    private static final long MB = 1024 * 1024;

    @Test
    void retention() throws Exception {
        String rel =
            System.getProperty("key.mt.retention.proof", "standard_key/java_dl/symmArray.key");
        int reps = Integer.getInteger("key.mt.retention.reps", 12);
        boolean histo = Boolean.getBoolean("key.mt.retention.histo");

        Path examples = FindResources.getExampleDirectory();
        if (examples == null) {
            System.out.println("[retention] examples directory not found; nothing to do");
            return;
        }
        Path keyFile = examples.resolve(rel);
        if (!Files.exists(keyFile)) {
            System.out.printf("[retention] missing proof %s%n", rel);
            return;
        }

        System.out.printf("[retention] proof=%s reps=%d maxHeap=%dMB histo=%s%n", rel, reps,
            Runtime.getRuntime().maxMemory() / MB, histo);

        boolean findRoot = Boolean.getBoolean("key.mt.retention.root");

        Map<String, Long> histoEarly = null;
        long[] usedMb = new long[reps];
        Proof retainedTarget = null; // stack-local only: the genuine leak path is the only one
                                     // found
        for (int i = 0; i < reps; i++) {
            KeYEnvironment<?> env = KeYEnvironment.load(keyFile);
            Proof proof = null;
            try {
                proof = env.getLoadedProof();
                ProofStarter starter = new ProofStarter(false);
                starter.init(proof);
                starter.start();
            } finally {
                env.dispose();
            }
            if (findRoot && i == 0) {
                retainedTarget = proof; // a disposed proof; we will hunt its static referrer
            }
            usedMb[i] = usedAfterGc() / MB;
            System.out.printf("[retention] rep=%-2d liveMB=%d%n", i, usedMb[i]);
            if (histo && i == 1) {
                histoEarly = classHistogram();
            }
        }

        long first = usedMb[0];
        long last = usedMb[reps - 1];
        double perRep = reps > 1 ? (double) (last - first) / (reps - 1) : 0.0;
        System.out.printf("[retention] RESULT first=%dMB last=%dMB delta=%dMB (%+.1f MB/proof)%n",
            first, last, last - first, perRep);
        System.out.printf("[retention] verdict: %s%n",
            perRep > 2.0 ? "RETENTION (live heap grows across disposed proofs)"
                    : "flat (dispose releases per-proof state)");

        if (histo && histoEarly != null) {
            printGrowth(histoEarly, classHistogram());
        }

        String dump = System.getProperty("key.mt.retention.dump");
        if (dump != null) {
            usedAfterGc(); // settle before dumping
            dumpHeap(dump);
        }

        if (findRoot && retainedTarget != null) {
            usedAfterGc();
            HeapRootFinder.reportPath(retainedTarget);
        }
    }

    /** Writes a live-objects-only HPROF heap dump for Eclipse MAT analysis. */
    private static void dumpHeap(String path) {
        try {
            Path p = Path.of(path);
            Files.deleteIfExists(p);
            Object bean = ManagementFactory.newPlatformMXBeanProxy(
                ManagementFactory.getPlatformMBeanServer(),
                "com.sun.management:type=HotSpotDiagnostic",
                Class.forName("com.sun.management.HotSpotDiagnosticMXBean"));
            bean.getClass().getMethod("dumpHeap", String.class, boolean.class)
                    .invoke(bean, p.toAbsolutePath().toString(), true);
            System.out.printf("[retention] heap dump written: %s%n", p.toAbsolutePath());
        } catch (Exception e) {
            System.out.println("[retention] heap dump failed: " + e);
        }
    }

    /** Live heap after several full GCs, to drain finalizers/soft refs as far as is practical. */
    private static long usedAfterGc() throws InterruptedException {
        Runtime rt = Runtime.getRuntime();
        for (int k = 0; k < 5; k++) {
            System.gc();
            Thread.sleep(120);
        }
        return rt.totalMemory() - rt.freeMemory();
    }

    /** class name -> live instance count, via the JVM's GC.class_histogram diagnostic command. */
    private static Map<String, Long> classHistogram() {
        Map<String, Long> m = new TreeMap<>();
        try {
            String out = (String) ManagementFactory.getPlatformMBeanServer().invoke(
                new javax.management.ObjectName("com.sun.management:type=DiagnosticCommand"),
                "gcClassHistogram", new Object[] { new String[0] },
                new String[] { String[].class.getName() });
            for (String line : out.split("\n")) {
                String[] p = line.trim().split("\\s+");
                // columns: num #instances #bytes class name
                if (p.length >= 4 && p[0].endsWith(":")) {
                    try {
                        m.put(p[3], Long.parseLong(p[1]));
                    } catch (NumberFormatException ignore) {
                        // header / non-data line
                    }
                }
            }
        } catch (Exception e) {
            System.out.println("[retention] histogram unavailable: " + e);
        }
        return m;
    }

    private static void printGrowth(Map<String, Long> early, Map<String, Long> late) {
        record Growth(String cls, long delta, long late) {
        }
        var list = new java.util.ArrayList<Growth>();
        for (var e : late.entrySet()) {
            long d = e.getValue() - early.getOrDefault(e.getKey(), 0L);
            if (d > 0) {
                list.add(new Growth(e.getKey(), d, e.getValue()));
            }
        }
        list.sort(Comparator.comparingLong((Growth g) -> g.delta).reversed());
        System.out.println("[retention] top live-instance growth (rep1 -> final):");
        for (int i = 0; i < Math.min(25, list.size()); i++) {
            Growth g = list.get(i);
            System.out.printf("[retention]   +%-10d (now %-10d) %s%n", g.delta, g.late, g.cls);
        }
    }
}

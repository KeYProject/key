/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.mtprobe;

import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

/**
 * The single point every divergence site reports to.
 * <p>
 * A "site" is a place in the prover where determinism can be measured. Two kinds exist:
 * <ul>
 * <li>a <em>comparison</em> site reports {@code observe(site, key, value)}: the same logical
 * decision (identified by {@code key}) should produce the same {@code value} in every run; the
 * tool later diffs one run against another (single-core vs multi-core) to find where they differ;
 * <li>an <em>invariant</em> site reports {@code invariantViolated(site, detail)}: an internal
 * determinism check tripped during a single run (for example the choice-point guard), so the
 * divergence is already proven and needs no second run to compare against.
 * </ul>
 * The agent-injected code and the driver both call the static methods here. It is deliberately
 * tiny and dependency-free so the bytecode the agent inlines into the prover can reach it.
 */
public final class ProbeSink {

    /** The sites the user turned on (e.g. {@code choice-point}); empty means nothing is recorded. */
    private static final Set<String> ENABLED = ConcurrentHashMap.newKeySet();

    /** The run currently being recorded; set by the driver before it proves. */
    private static volatile ProbeRun current;

    private ProbeSink() {
    }

    /** Turns on the given comma-separated sites (parsed from the agent argument). */
    public static void enableSites(String csv) {
        if (csv == null || csv.isBlank()) {
            return;
        }
        for (String s : csv.split(",")) {
            if (!s.isBlank()) {
                ENABLED.add(s.trim());
            }
        }
    }

    /** @return whether {@code site} is turned on */
    public static boolean isEnabled(String site) {
        return ENABLED.contains(site);
    }

    /** @return the enabled sites, for the report header */
    public static Set<String> enabledSites() {
        return Set.copyOf(ENABLED);
    }

    /** Begins recording a new run under {@code label} and returns it. */
    public static ProbeRun startRun(String label) {
        final ProbeRun run = new ProbeRun(label);
        current = run;
        return run;
    }

    /** Stops recording (so proving outside a measured run costs nothing). */
    public static void endRun() {
        current = null;
    }

    /**
     * A comparison site reports that the decision identified by {@code key} produced {@code value}.
     * Called concurrently by worker threads, so it is thread-safe.
     */
    public static void observe(String site, String key, String value) {
        final ProbeRun run = current;
        if (run != null && ENABLED.contains(site)) {
            run.observe(site, key, value);
        }
    }

    /**
     * An invariant site reports that a determinism check <em>tripped</em> during the current run --
     * a hard finding (for example the choice-point guard).
     */
    public static void invariantViolated(String site, String detail) {
        final ProbeRun run = current;
        if (run != null && ENABLED.contains(site)) {
            run.invariantViolated(site, detail);
        }
    }

    /**
     * A site reports a <em>latent risk</em>, not a proven divergence -- something that could make
     * proof search order-dependent but usually does not (for example a rule-cost tie). These are
     * counted separately from violations so they do not look like bugs; they happen in the
     * single-core baseline too.
     */
    public static void warn(String site, String detail) {
        final ProbeRun run = current;
        if (run != null && ENABLED.contains(site)) {
            run.warn(site, detail);
        }
    }
}
